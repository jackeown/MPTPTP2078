%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:09 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  191 (2172 expanded)
%              Number of clauses        :  106 ( 610 expanded)
%              Number of leaves         :   21 ( 538 expanded)
%              Depth                    :   28
%              Number of atoms          :  675 (15039 expanded)
%              Number of equality atoms :  265 (1255 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK3,X0,X0)
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
          ( ~ r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2))
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v3_funct_2(X2,sK1,sK1)
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK3,sK1,sK1)
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f53,f52])).

fof(f88,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f5,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f62,f75,f75])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k6_partfun1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f97,plain,(
    ! [X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1926,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1922,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_369,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_381,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_369,c_8])).

cnf(c_1917,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_2914,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_2(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1917])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_475,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_476,plain,
    ( v2_funct_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_478,plain,
    ( v2_funct_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_33,c_30])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(X0) = X2
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_478])).

cnf(c_636,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | k2_relat_1(sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_3422,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2914,c_30,c_638])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1932,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3013,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1922,c_1932])).

cnf(c_3425,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3422,c_3013])).

cnf(c_22,plain,
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
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_21])).

cnf(c_184,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_1919,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_3650,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_1919])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5193,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3650,c_34,c_35,c_37])).

cnf(c_5194,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5193])).

cnf(c_5205,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_5194])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5206,plain,
    ( ~ v1_funct_2(sK3,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5205])).

cnf(c_5346,plain,
    ( sK1 = k1_xboole_0
    | k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_38,c_39,c_41])).

cnf(c_5347,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5346])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1927,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_495,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_33,c_32,c_30])).

cnf(c_1965,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1927,c_497])).

cnf(c_5350,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_1965])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2171,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2172,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2171])).

cnf(c_5353,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5350,c_41,c_2172])).

cnf(c_5376,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5353,c_1965])).

cnf(c_2,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_7,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2280,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_7])).

cnf(c_2281,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2280,c_2])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1928,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3553,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1928])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1933,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3022,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1922,c_1933])).

cnf(c_3557,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3553,c_3022])).

cnf(c_3655,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3557,c_34,c_35])).

cnf(c_4,plain,
    ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1937,plain,
    ( k6_partfun1(k1_relat_1(X0)) = X0
    | r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3660,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3655,c_1937])).

cnf(c_3666,plain,
    ( k6_partfun1(sK1) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3660,c_3655])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2144])).

cnf(c_5067,plain,
    ( k6_partfun1(sK1) = sK2
    | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3666,c_34,c_37,c_2145])).

cnf(c_5359,plain,
    ( k6_partfun1(k1_xboole_0) = sK2
    | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5353,c_5067])).

cnf(c_5459,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5359,c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1918,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_5547,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5459,c_1918])).

cnf(c_1925,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3552,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_1928])).

cnf(c_3021,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1925,c_1933])).

cnf(c_3564,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3552,c_3021])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3819,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3564,c_38,c_39])).

cnf(c_3824,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3819,c_1937])).

cnf(c_3830,plain,
    ( k6_partfun1(sK1) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3824,c_3819])).

cnf(c_2141,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2142,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2141])).

cnf(c_5076,plain,
    ( k6_partfun1(sK1) = sK3
    | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_38,c_41,c_2142])).

cnf(c_5358,plain,
    ( k6_partfun1(k1_xboole_0) = sK3
    | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5353,c_5076])).

cnf(c_5464,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5358,c_2])).

cnf(c_5646,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5464,c_1918])).

cnf(c_6138,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5376,c_2281,c_5547,c_5646])).

cnf(c_5380,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5353,c_1925])).

cnf(c_5907,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5380,c_5646])).

cnf(c_1931,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5914,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5907,c_1931])).

cnf(c_6140,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6138,c_5914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:28:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.01  
% 3.12/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/1.01  
% 3.12/1.01  ------  iProver source info
% 3.12/1.01  
% 3.12/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.12/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/1.01  git: non_committed_changes: false
% 3.12/1.01  git: last_make_outside_of_git: false
% 3.12/1.01  
% 3.12/1.01  ------ 
% 3.12/1.01  
% 3.12/1.01  ------ Input Options
% 3.12/1.01  
% 3.12/1.01  --out_options                           all
% 3.12/1.01  --tptp_safe_out                         true
% 3.12/1.01  --problem_path                          ""
% 3.12/1.01  --include_path                          ""
% 3.12/1.01  --clausifier                            res/vclausify_rel
% 3.12/1.01  --clausifier_options                    --mode clausify
% 3.12/1.01  --stdin                                 false
% 3.12/1.01  --stats_out                             all
% 3.12/1.01  
% 3.12/1.01  ------ General Options
% 3.12/1.01  
% 3.12/1.01  --fof                                   false
% 3.12/1.01  --time_out_real                         305.
% 3.12/1.01  --time_out_virtual                      -1.
% 3.12/1.01  --symbol_type_check                     false
% 3.12/1.01  --clausify_out                          false
% 3.12/1.01  --sig_cnt_out                           false
% 3.12/1.01  --trig_cnt_out                          false
% 3.12/1.01  --trig_cnt_out_tolerance                1.
% 3.12/1.01  --trig_cnt_out_sk_spl                   false
% 3.12/1.01  --abstr_cl_out                          false
% 3.12/1.01  
% 3.12/1.01  ------ Global Options
% 3.12/1.01  
% 3.12/1.01  --schedule                              default
% 3.12/1.01  --add_important_lit                     false
% 3.12/1.01  --prop_solver_per_cl                    1000
% 3.12/1.01  --min_unsat_core                        false
% 3.12/1.01  --soft_assumptions                      false
% 3.12/1.01  --soft_lemma_size                       3
% 3.12/1.01  --prop_impl_unit_size                   0
% 3.12/1.01  --prop_impl_unit                        []
% 3.12/1.01  --share_sel_clauses                     true
% 3.12/1.01  --reset_solvers                         false
% 3.12/1.01  --bc_imp_inh                            [conj_cone]
% 3.12/1.01  --conj_cone_tolerance                   3.
% 3.12/1.01  --extra_neg_conj                        none
% 3.12/1.01  --large_theory_mode                     true
% 3.12/1.01  --prolific_symb_bound                   200
% 3.12/1.01  --lt_threshold                          2000
% 3.12/1.01  --clause_weak_htbl                      true
% 3.12/1.01  --gc_record_bc_elim                     false
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing Options
% 3.12/1.01  
% 3.12/1.01  --preprocessing_flag                    true
% 3.12/1.01  --time_out_prep_mult                    0.1
% 3.12/1.01  --splitting_mode                        input
% 3.12/1.01  --splitting_grd                         true
% 3.12/1.01  --splitting_cvd                         false
% 3.12/1.01  --splitting_cvd_svl                     false
% 3.12/1.01  --splitting_nvd                         32
% 3.12/1.01  --sub_typing                            true
% 3.12/1.01  --prep_gs_sim                           true
% 3.12/1.01  --prep_unflatten                        true
% 3.12/1.01  --prep_res_sim                          true
% 3.12/1.01  --prep_upred                            true
% 3.12/1.01  --prep_sem_filter                       exhaustive
% 3.12/1.01  --prep_sem_filter_out                   false
% 3.12/1.01  --pred_elim                             true
% 3.12/1.01  --res_sim_input                         true
% 3.12/1.01  --eq_ax_congr_red                       true
% 3.12/1.01  --pure_diseq_elim                       true
% 3.12/1.01  --brand_transform                       false
% 3.12/1.01  --non_eq_to_eq                          false
% 3.12/1.01  --prep_def_merge                        true
% 3.12/1.01  --prep_def_merge_prop_impl              false
% 3.12/1.01  --prep_def_merge_mbd                    true
% 3.12/1.01  --prep_def_merge_tr_red                 false
% 3.12/1.01  --prep_def_merge_tr_cl                  false
% 3.12/1.01  --smt_preprocessing                     true
% 3.12/1.01  --smt_ac_axioms                         fast
% 3.12/1.01  --preprocessed_out                      false
% 3.12/1.01  --preprocessed_stats                    false
% 3.12/1.01  
% 3.12/1.01  ------ Abstraction refinement Options
% 3.12/1.01  
% 3.12/1.01  --abstr_ref                             []
% 3.12/1.01  --abstr_ref_prep                        false
% 3.12/1.01  --abstr_ref_until_sat                   false
% 3.12/1.01  --abstr_ref_sig_restrict                funpre
% 3.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.01  --abstr_ref_under                       []
% 3.12/1.01  
% 3.12/1.01  ------ SAT Options
% 3.12/1.01  
% 3.12/1.01  --sat_mode                              false
% 3.12/1.01  --sat_fm_restart_options                ""
% 3.12/1.01  --sat_gr_def                            false
% 3.12/1.01  --sat_epr_types                         true
% 3.12/1.01  --sat_non_cyclic_types                  false
% 3.12/1.01  --sat_finite_models                     false
% 3.12/1.01  --sat_fm_lemmas                         false
% 3.12/1.01  --sat_fm_prep                           false
% 3.12/1.01  --sat_fm_uc_incr                        true
% 3.12/1.01  --sat_out_model                         small
% 3.12/1.01  --sat_out_clauses                       false
% 3.12/1.01  
% 3.12/1.01  ------ QBF Options
% 3.12/1.01  
% 3.12/1.01  --qbf_mode                              false
% 3.12/1.01  --qbf_elim_univ                         false
% 3.12/1.01  --qbf_dom_inst                          none
% 3.12/1.01  --qbf_dom_pre_inst                      false
% 3.12/1.01  --qbf_sk_in                             false
% 3.12/1.01  --qbf_pred_elim                         true
% 3.12/1.01  --qbf_split                             512
% 3.12/1.01  
% 3.12/1.01  ------ BMC1 Options
% 3.12/1.01  
% 3.12/1.01  --bmc1_incremental                      false
% 3.12/1.01  --bmc1_axioms                           reachable_all
% 3.12/1.01  --bmc1_min_bound                        0
% 3.12/1.01  --bmc1_max_bound                        -1
% 3.12/1.01  --bmc1_max_bound_default                -1
% 3.12/1.01  --bmc1_symbol_reachability              true
% 3.12/1.01  --bmc1_property_lemmas                  false
% 3.12/1.01  --bmc1_k_induction                      false
% 3.12/1.01  --bmc1_non_equiv_states                 false
% 3.12/1.01  --bmc1_deadlock                         false
% 3.12/1.01  --bmc1_ucm                              false
% 3.12/1.01  --bmc1_add_unsat_core                   none
% 3.12/1.01  --bmc1_unsat_core_children              false
% 3.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.01  --bmc1_out_stat                         full
% 3.12/1.01  --bmc1_ground_init                      false
% 3.12/1.01  --bmc1_pre_inst_next_state              false
% 3.12/1.01  --bmc1_pre_inst_state                   false
% 3.12/1.01  --bmc1_pre_inst_reach_state             false
% 3.12/1.01  --bmc1_out_unsat_core                   false
% 3.12/1.01  --bmc1_aig_witness_out                  false
% 3.12/1.01  --bmc1_verbose                          false
% 3.12/1.01  --bmc1_dump_clauses_tptp                false
% 3.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.01  --bmc1_dump_file                        -
% 3.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.01  --bmc1_ucm_extend_mode                  1
% 3.12/1.01  --bmc1_ucm_init_mode                    2
% 3.12/1.01  --bmc1_ucm_cone_mode                    none
% 3.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.01  --bmc1_ucm_relax_model                  4
% 3.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.01  --bmc1_ucm_layered_model                none
% 3.12/1.01  --bmc1_ucm_max_lemma_size               10
% 3.12/1.01  
% 3.12/1.01  ------ AIG Options
% 3.12/1.01  
% 3.12/1.01  --aig_mode                              false
% 3.12/1.01  
% 3.12/1.01  ------ Instantiation Options
% 3.12/1.01  
% 3.12/1.01  --instantiation_flag                    true
% 3.12/1.01  --inst_sos_flag                         false
% 3.12/1.01  --inst_sos_phase                        true
% 3.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.01  --inst_lit_sel_side                     num_symb
% 3.12/1.01  --inst_solver_per_active                1400
% 3.12/1.01  --inst_solver_calls_frac                1.
% 3.12/1.01  --inst_passive_queue_type               priority_queues
% 3.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.01  --inst_passive_queues_freq              [25;2]
% 3.12/1.01  --inst_dismatching                      true
% 3.12/1.01  --inst_eager_unprocessed_to_passive     true
% 3.12/1.01  --inst_prop_sim_given                   true
% 3.12/1.01  --inst_prop_sim_new                     false
% 3.12/1.01  --inst_subs_new                         false
% 3.12/1.01  --inst_eq_res_simp                      false
% 3.12/1.01  --inst_subs_given                       false
% 3.12/1.01  --inst_orphan_elimination               true
% 3.12/1.01  --inst_learning_loop_flag               true
% 3.12/1.01  --inst_learning_start                   3000
% 3.12/1.01  --inst_learning_factor                  2
% 3.12/1.01  --inst_start_prop_sim_after_learn       3
% 3.12/1.01  --inst_sel_renew                        solver
% 3.12/1.01  --inst_lit_activity_flag                true
% 3.12/1.01  --inst_restr_to_given                   false
% 3.12/1.01  --inst_activity_threshold               500
% 3.12/1.01  --inst_out_proof                        true
% 3.12/1.01  
% 3.12/1.01  ------ Resolution Options
% 3.12/1.01  
% 3.12/1.01  --resolution_flag                       true
% 3.12/1.01  --res_lit_sel                           adaptive
% 3.12/1.01  --res_lit_sel_side                      none
% 3.12/1.01  --res_ordering                          kbo
% 3.12/1.01  --res_to_prop_solver                    active
% 3.12/1.01  --res_prop_simpl_new                    false
% 3.12/1.01  --res_prop_simpl_given                  true
% 3.12/1.01  --res_passive_queue_type                priority_queues
% 3.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.01  --res_passive_queues_freq               [15;5]
% 3.12/1.01  --res_forward_subs                      full
% 3.12/1.01  --res_backward_subs                     full
% 3.12/1.01  --res_forward_subs_resolution           true
% 3.12/1.01  --res_backward_subs_resolution          true
% 3.12/1.01  --res_orphan_elimination                true
% 3.12/1.01  --res_time_limit                        2.
% 3.12/1.01  --res_out_proof                         true
% 3.12/1.01  
% 3.12/1.01  ------ Superposition Options
% 3.12/1.01  
% 3.12/1.01  --superposition_flag                    true
% 3.12/1.01  --sup_passive_queue_type                priority_queues
% 3.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.01  --demod_completeness_check              fast
% 3.12/1.01  --demod_use_ground                      true
% 3.12/1.01  --sup_to_prop_solver                    passive
% 3.12/1.01  --sup_prop_simpl_new                    true
% 3.12/1.01  --sup_prop_simpl_given                  true
% 3.12/1.01  --sup_fun_splitting                     false
% 3.12/1.01  --sup_smt_interval                      50000
% 3.12/1.01  
% 3.12/1.01  ------ Superposition Simplification Setup
% 3.12/1.01  
% 3.12/1.01  --sup_indices_passive                   []
% 3.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_full_bw                           [BwDemod]
% 3.12/1.01  --sup_immed_triv                        [TrivRules]
% 3.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_immed_bw_main                     []
% 3.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.01  
% 3.12/1.01  ------ Combination Options
% 3.12/1.01  
% 3.12/1.01  --comb_res_mult                         3
% 3.12/1.01  --comb_sup_mult                         2
% 3.12/1.01  --comb_inst_mult                        10
% 3.12/1.01  
% 3.12/1.01  ------ Debug Options
% 3.12/1.01  
% 3.12/1.01  --dbg_backtrace                         false
% 3.12/1.01  --dbg_dump_prop_clauses                 false
% 3.12/1.01  --dbg_dump_prop_clauses_file            -
% 3.12/1.01  --dbg_out_stat                          false
% 3.12/1.01  ------ Parsing...
% 3.12/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/1.01  ------ Proving...
% 3.12/1.01  ------ Problem Properties 
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  clauses                                 29
% 3.12/1.01  conjectures                             8
% 3.12/1.01  EPR                                     7
% 3.12/1.01  Horn                                    27
% 3.12/1.01  unary                                   15
% 3.12/1.01  binary                                  5
% 3.12/1.01  lits                                    70
% 3.12/1.01  lits eq                                 18
% 3.12/1.01  fd_pure                                 0
% 3.12/1.01  fd_pseudo                               0
% 3.12/1.01  fd_cond                                 0
% 3.12/1.01  fd_pseudo_cond                          3
% 3.12/1.01  AC symbols                              0
% 3.12/1.01  
% 3.12/1.01  ------ Schedule dynamic 5 is on 
% 3.12/1.01  
% 3.12/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  ------ 
% 3.12/1.01  Current options:
% 3.12/1.01  ------ 
% 3.12/1.01  
% 3.12/1.01  ------ Input Options
% 3.12/1.01  
% 3.12/1.01  --out_options                           all
% 3.12/1.01  --tptp_safe_out                         true
% 3.12/1.01  --problem_path                          ""
% 3.12/1.01  --include_path                          ""
% 3.12/1.01  --clausifier                            res/vclausify_rel
% 3.12/1.01  --clausifier_options                    --mode clausify
% 3.12/1.01  --stdin                                 false
% 3.12/1.01  --stats_out                             all
% 3.12/1.01  
% 3.12/1.01  ------ General Options
% 3.12/1.01  
% 3.12/1.01  --fof                                   false
% 3.12/1.01  --time_out_real                         305.
% 3.12/1.01  --time_out_virtual                      -1.
% 3.12/1.01  --symbol_type_check                     false
% 3.12/1.01  --clausify_out                          false
% 3.12/1.01  --sig_cnt_out                           false
% 3.12/1.01  --trig_cnt_out                          false
% 3.12/1.01  --trig_cnt_out_tolerance                1.
% 3.12/1.01  --trig_cnt_out_sk_spl                   false
% 3.12/1.01  --abstr_cl_out                          false
% 3.12/1.01  
% 3.12/1.01  ------ Global Options
% 3.12/1.01  
% 3.12/1.01  --schedule                              default
% 3.12/1.01  --add_important_lit                     false
% 3.12/1.01  --prop_solver_per_cl                    1000
% 3.12/1.01  --min_unsat_core                        false
% 3.12/1.01  --soft_assumptions                      false
% 3.12/1.01  --soft_lemma_size                       3
% 3.12/1.01  --prop_impl_unit_size                   0
% 3.12/1.01  --prop_impl_unit                        []
% 3.12/1.01  --share_sel_clauses                     true
% 3.12/1.01  --reset_solvers                         false
% 3.12/1.01  --bc_imp_inh                            [conj_cone]
% 3.12/1.01  --conj_cone_tolerance                   3.
% 3.12/1.01  --extra_neg_conj                        none
% 3.12/1.01  --large_theory_mode                     true
% 3.12/1.01  --prolific_symb_bound                   200
% 3.12/1.01  --lt_threshold                          2000
% 3.12/1.01  --clause_weak_htbl                      true
% 3.12/1.01  --gc_record_bc_elim                     false
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing Options
% 3.12/1.01  
% 3.12/1.01  --preprocessing_flag                    true
% 3.12/1.01  --time_out_prep_mult                    0.1
% 3.12/1.01  --splitting_mode                        input
% 3.12/1.01  --splitting_grd                         true
% 3.12/1.01  --splitting_cvd                         false
% 3.12/1.01  --splitting_cvd_svl                     false
% 3.12/1.01  --splitting_nvd                         32
% 3.12/1.01  --sub_typing                            true
% 3.12/1.01  --prep_gs_sim                           true
% 3.12/1.01  --prep_unflatten                        true
% 3.12/1.01  --prep_res_sim                          true
% 3.12/1.01  --prep_upred                            true
% 3.12/1.01  --prep_sem_filter                       exhaustive
% 3.12/1.01  --prep_sem_filter_out                   false
% 3.12/1.01  --pred_elim                             true
% 3.12/1.01  --res_sim_input                         true
% 3.12/1.01  --eq_ax_congr_red                       true
% 3.12/1.01  --pure_diseq_elim                       true
% 3.12/1.01  --brand_transform                       false
% 3.12/1.01  --non_eq_to_eq                          false
% 3.12/1.01  --prep_def_merge                        true
% 3.12/1.01  --prep_def_merge_prop_impl              false
% 3.12/1.01  --prep_def_merge_mbd                    true
% 3.12/1.01  --prep_def_merge_tr_red                 false
% 3.12/1.01  --prep_def_merge_tr_cl                  false
% 3.12/1.01  --smt_preprocessing                     true
% 3.12/1.01  --smt_ac_axioms                         fast
% 3.12/1.01  --preprocessed_out                      false
% 3.12/1.01  --preprocessed_stats                    false
% 3.12/1.01  
% 3.12/1.01  ------ Abstraction refinement Options
% 3.12/1.01  
% 3.12/1.01  --abstr_ref                             []
% 3.12/1.01  --abstr_ref_prep                        false
% 3.12/1.01  --abstr_ref_until_sat                   false
% 3.12/1.01  --abstr_ref_sig_restrict                funpre
% 3.12/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.01  --abstr_ref_under                       []
% 3.12/1.01  
% 3.12/1.01  ------ SAT Options
% 3.12/1.01  
% 3.12/1.01  --sat_mode                              false
% 3.12/1.01  --sat_fm_restart_options                ""
% 3.12/1.01  --sat_gr_def                            false
% 3.12/1.01  --sat_epr_types                         true
% 3.12/1.01  --sat_non_cyclic_types                  false
% 3.12/1.01  --sat_finite_models                     false
% 3.12/1.01  --sat_fm_lemmas                         false
% 3.12/1.01  --sat_fm_prep                           false
% 3.12/1.01  --sat_fm_uc_incr                        true
% 3.12/1.01  --sat_out_model                         small
% 3.12/1.01  --sat_out_clauses                       false
% 3.12/1.01  
% 3.12/1.01  ------ QBF Options
% 3.12/1.01  
% 3.12/1.01  --qbf_mode                              false
% 3.12/1.01  --qbf_elim_univ                         false
% 3.12/1.01  --qbf_dom_inst                          none
% 3.12/1.01  --qbf_dom_pre_inst                      false
% 3.12/1.01  --qbf_sk_in                             false
% 3.12/1.01  --qbf_pred_elim                         true
% 3.12/1.01  --qbf_split                             512
% 3.12/1.01  
% 3.12/1.01  ------ BMC1 Options
% 3.12/1.01  
% 3.12/1.01  --bmc1_incremental                      false
% 3.12/1.01  --bmc1_axioms                           reachable_all
% 3.12/1.01  --bmc1_min_bound                        0
% 3.12/1.01  --bmc1_max_bound                        -1
% 3.12/1.01  --bmc1_max_bound_default                -1
% 3.12/1.01  --bmc1_symbol_reachability              true
% 3.12/1.01  --bmc1_property_lemmas                  false
% 3.12/1.01  --bmc1_k_induction                      false
% 3.12/1.01  --bmc1_non_equiv_states                 false
% 3.12/1.01  --bmc1_deadlock                         false
% 3.12/1.01  --bmc1_ucm                              false
% 3.12/1.01  --bmc1_add_unsat_core                   none
% 3.12/1.01  --bmc1_unsat_core_children              false
% 3.12/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.01  --bmc1_out_stat                         full
% 3.12/1.01  --bmc1_ground_init                      false
% 3.12/1.01  --bmc1_pre_inst_next_state              false
% 3.12/1.01  --bmc1_pre_inst_state                   false
% 3.12/1.01  --bmc1_pre_inst_reach_state             false
% 3.12/1.01  --bmc1_out_unsat_core                   false
% 3.12/1.01  --bmc1_aig_witness_out                  false
% 3.12/1.01  --bmc1_verbose                          false
% 3.12/1.01  --bmc1_dump_clauses_tptp                false
% 3.12/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.01  --bmc1_dump_file                        -
% 3.12/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.01  --bmc1_ucm_extend_mode                  1
% 3.12/1.01  --bmc1_ucm_init_mode                    2
% 3.12/1.01  --bmc1_ucm_cone_mode                    none
% 3.12/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.01  --bmc1_ucm_relax_model                  4
% 3.12/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.01  --bmc1_ucm_layered_model                none
% 3.12/1.01  --bmc1_ucm_max_lemma_size               10
% 3.12/1.01  
% 3.12/1.01  ------ AIG Options
% 3.12/1.01  
% 3.12/1.01  --aig_mode                              false
% 3.12/1.01  
% 3.12/1.01  ------ Instantiation Options
% 3.12/1.01  
% 3.12/1.01  --instantiation_flag                    true
% 3.12/1.01  --inst_sos_flag                         false
% 3.12/1.01  --inst_sos_phase                        true
% 3.12/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.01  --inst_lit_sel_side                     none
% 3.12/1.01  --inst_solver_per_active                1400
% 3.12/1.01  --inst_solver_calls_frac                1.
% 3.12/1.01  --inst_passive_queue_type               priority_queues
% 3.12/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.01  --inst_passive_queues_freq              [25;2]
% 3.12/1.01  --inst_dismatching                      true
% 3.12/1.01  --inst_eager_unprocessed_to_passive     true
% 3.12/1.01  --inst_prop_sim_given                   true
% 3.12/1.01  --inst_prop_sim_new                     false
% 3.12/1.01  --inst_subs_new                         false
% 3.12/1.01  --inst_eq_res_simp                      false
% 3.12/1.01  --inst_subs_given                       false
% 3.12/1.01  --inst_orphan_elimination               true
% 3.12/1.01  --inst_learning_loop_flag               true
% 3.12/1.01  --inst_learning_start                   3000
% 3.12/1.01  --inst_learning_factor                  2
% 3.12/1.01  --inst_start_prop_sim_after_learn       3
% 3.12/1.01  --inst_sel_renew                        solver
% 3.12/1.01  --inst_lit_activity_flag                true
% 3.12/1.01  --inst_restr_to_given                   false
% 3.12/1.01  --inst_activity_threshold               500
% 3.12/1.01  --inst_out_proof                        true
% 3.12/1.01  
% 3.12/1.01  ------ Resolution Options
% 3.12/1.01  
% 3.12/1.01  --resolution_flag                       false
% 3.12/1.01  --res_lit_sel                           adaptive
% 3.12/1.01  --res_lit_sel_side                      none
% 3.12/1.01  --res_ordering                          kbo
% 3.12/1.01  --res_to_prop_solver                    active
% 3.12/1.01  --res_prop_simpl_new                    false
% 3.12/1.01  --res_prop_simpl_given                  true
% 3.12/1.01  --res_passive_queue_type                priority_queues
% 3.12/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.01  --res_passive_queues_freq               [15;5]
% 3.12/1.01  --res_forward_subs                      full
% 3.12/1.01  --res_backward_subs                     full
% 3.12/1.01  --res_forward_subs_resolution           true
% 3.12/1.01  --res_backward_subs_resolution          true
% 3.12/1.01  --res_orphan_elimination                true
% 3.12/1.01  --res_time_limit                        2.
% 3.12/1.01  --res_out_proof                         true
% 3.12/1.01  
% 3.12/1.01  ------ Superposition Options
% 3.12/1.01  
% 3.12/1.01  --superposition_flag                    true
% 3.12/1.01  --sup_passive_queue_type                priority_queues
% 3.12/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.01  --demod_completeness_check              fast
% 3.12/1.01  --demod_use_ground                      true
% 3.12/1.01  --sup_to_prop_solver                    passive
% 3.12/1.01  --sup_prop_simpl_new                    true
% 3.12/1.01  --sup_prop_simpl_given                  true
% 3.12/1.01  --sup_fun_splitting                     false
% 3.12/1.01  --sup_smt_interval                      50000
% 3.12/1.01  
% 3.12/1.01  ------ Superposition Simplification Setup
% 3.12/1.01  
% 3.12/1.01  --sup_indices_passive                   []
% 3.12/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_full_bw                           [BwDemod]
% 3.12/1.01  --sup_immed_triv                        [TrivRules]
% 3.12/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_immed_bw_main                     []
% 3.12/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.01  
% 3.12/1.01  ------ Combination Options
% 3.12/1.01  
% 3.12/1.01  --comb_res_mult                         3
% 3.12/1.01  --comb_sup_mult                         2
% 3.12/1.01  --comb_inst_mult                        10
% 3.12/1.01  
% 3.12/1.01  ------ Debug Options
% 3.12/1.01  
% 3.12/1.01  --dbg_backtrace                         false
% 3.12/1.01  --dbg_dump_prop_clauses                 false
% 3.12/1.01  --dbg_dump_prop_clauses_file            -
% 3.12/1.01  --dbg_out_stat                          false
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  ------ Proving...
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  % SZS status Theorem for theBenchmark.p
% 3.12/1.01  
% 3.12/1.01   Resolution empty clause
% 3.12/1.01  
% 3.12/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/1.01  
% 3.12/1.01  fof(f18,conjecture,(
% 3.12/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f19,negated_conjecture,(
% 3.12/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.12/1.01    inference(negated_conjecture,[],[f18])).
% 3.12/1.01  
% 3.12/1.01  fof(f43,plain,(
% 3.12/1.01    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.12/1.01    inference(ennf_transformation,[],[f19])).
% 3.12/1.01  
% 3.12/1.01  fof(f44,plain,(
% 3.12/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.12/1.01    inference(flattening,[],[f43])).
% 3.12/1.01  
% 3.12/1.01  fof(f53,plain,(
% 3.12/1.01    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.12/1.01    introduced(choice_axiom,[])).
% 3.12/1.01  
% 3.12/1.01  fof(f52,plain,(
% 3.12/1.01    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.12/1.01    introduced(choice_axiom,[])).
% 3.12/1.01  
% 3.12/1.01  fof(f54,plain,(
% 3.12/1.01    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f53,f52])).
% 3.12/1.01  
% 3.12/1.01  fof(f88,plain,(
% 3.12/1.01    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f83,plain,(
% 3.12/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f7,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f21,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.12/1.01    inference(pure_predicate_removal,[],[f7])).
% 3.12/1.01  
% 3.12/1.01  fof(f26,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(ennf_transformation,[],[f21])).
% 3.12/1.01  
% 3.12/1.01  fof(f64,plain,(
% 3.12/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f26])).
% 3.12/1.01  
% 3.12/1.01  fof(f12,axiom,(
% 3.12/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f33,plain,(
% 3.12/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.12/1.01    inference(ennf_transformation,[],[f12])).
% 3.12/1.01  
% 3.12/1.01  fof(f34,plain,(
% 3.12/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(flattening,[],[f33])).
% 3.12/1.01  
% 3.12/1.01  fof(f51,plain,(
% 3.12/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(nnf_transformation,[],[f34])).
% 3.12/1.01  
% 3.12/1.01  fof(f72,plain,(
% 3.12/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f51])).
% 3.12/1.01  
% 3.12/1.01  fof(f6,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f25,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(ennf_transformation,[],[f6])).
% 3.12/1.01  
% 3.12/1.01  fof(f63,plain,(
% 3.12/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f25])).
% 3.12/1.01  
% 3.12/1.01  fof(f11,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f31,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(ennf_transformation,[],[f11])).
% 3.12/1.01  
% 3.12/1.01  fof(f32,plain,(
% 3.12/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(flattening,[],[f31])).
% 3.12/1.01  
% 3.12/1.01  fof(f71,plain,(
% 3.12/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f32])).
% 3.12/1.01  
% 3.12/1.01  fof(f82,plain,(
% 3.12/1.01    v3_funct_2(sK2,sK1,sK1)),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f80,plain,(
% 3.12/1.01    v1_funct_1(sK2)),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f9,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f28,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(ennf_transformation,[],[f9])).
% 3.12/1.01  
% 3.12/1.01  fof(f66,plain,(
% 3.12/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f28])).
% 3.12/1.01  
% 3.12/1.01  fof(f16,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f39,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.12/1.01    inference(ennf_transformation,[],[f16])).
% 3.12/1.01  
% 3.12/1.01  fof(f40,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.12/1.01    inference(flattening,[],[f39])).
% 3.12/1.01  
% 3.12/1.01  fof(f78,plain,(
% 3.12/1.01    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f40])).
% 3.12/1.01  
% 3.12/1.01  fof(f15,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f37,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.12/1.01    inference(ennf_transformation,[],[f15])).
% 3.12/1.01  
% 3.12/1.01  fof(f38,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.12/1.01    inference(flattening,[],[f37])).
% 3.12/1.01  
% 3.12/1.01  fof(f76,plain,(
% 3.12/1.01    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f38])).
% 3.12/1.01  
% 3.12/1.01  fof(f81,plain,(
% 3.12/1.01    v1_funct_2(sK2,sK1,sK1)),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f84,plain,(
% 3.12/1.01    v1_funct_1(sK3)),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f85,plain,(
% 3.12/1.01    v1_funct_2(sK3,sK1,sK1)),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f87,plain,(
% 3.12/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f89,plain,(
% 3.12/1.01    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.12/1.01    inference(cnf_transformation,[],[f54])).
% 3.12/1.01  
% 3.12/1.01  fof(f13,axiom,(
% 3.12/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f35,plain,(
% 3.12/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.12/1.01    inference(ennf_transformation,[],[f13])).
% 3.12/1.01  
% 3.12/1.01  fof(f36,plain,(
% 3.12/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.12/1.01    inference(flattening,[],[f35])).
% 3.12/1.01  
% 3.12/1.01  fof(f74,plain,(
% 3.12/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f36])).
% 3.12/1.01  
% 3.12/1.01  fof(f10,axiom,(
% 3.12/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f29,plain,(
% 3.12/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.12/1.01    inference(ennf_transformation,[],[f10])).
% 3.12/1.01  
% 3.12/1.01  fof(f30,plain,(
% 3.12/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(flattening,[],[f29])).
% 3.12/1.01  
% 3.12/1.01  fof(f50,plain,(
% 3.12/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(nnf_transformation,[],[f30])).
% 3.12/1.01  
% 3.12/1.01  fof(f68,plain,(
% 3.12/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f50])).
% 3.12/1.01  
% 3.12/1.01  fof(f100,plain,(
% 3.12/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(equality_resolution,[],[f68])).
% 3.12/1.01  
% 3.12/1.01  fof(f3,axiom,(
% 3.12/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f57,plain,(
% 3.12/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.12/1.01    inference(cnf_transformation,[],[f3])).
% 3.12/1.01  
% 3.12/1.01  fof(f14,axiom,(
% 3.12/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f75,plain,(
% 3.12/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f14])).
% 3.12/1.01  
% 3.12/1.01  fof(f90,plain,(
% 3.12/1.01    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.12/1.01    inference(definition_unfolding,[],[f57,f75])).
% 3.12/1.01  
% 3.12/1.01  fof(f5,axiom,(
% 3.12/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f62,plain,(
% 3.12/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f5])).
% 3.12/1.01  
% 3.12/1.01  fof(f95,plain,(
% 3.12/1.01    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.12/1.01    inference(definition_unfolding,[],[f62,f75,f75])).
% 3.12/1.01  
% 3.12/1.01  fof(f17,axiom,(
% 3.12/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f41,plain,(
% 3.12/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.12/1.01    inference(ennf_transformation,[],[f17])).
% 3.12/1.01  
% 3.12/1.01  fof(f42,plain,(
% 3.12/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.12/1.01    inference(flattening,[],[f41])).
% 3.12/1.01  
% 3.12/1.01  fof(f79,plain,(
% 3.12/1.01    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f42])).
% 3.12/1.01  
% 3.12/1.01  fof(f8,axiom,(
% 3.12/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f27,plain,(
% 3.12/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.01    inference(ennf_transformation,[],[f8])).
% 3.12/1.01  
% 3.12/1.01  fof(f65,plain,(
% 3.12/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.01    inference(cnf_transformation,[],[f27])).
% 3.12/1.01  
% 3.12/1.01  fof(f4,axiom,(
% 3.12/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f23,plain,(
% 3.12/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.12/1.01    inference(ennf_transformation,[],[f4])).
% 3.12/1.01  
% 3.12/1.01  fof(f24,plain,(
% 3.12/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(flattening,[],[f23])).
% 3.12/1.01  
% 3.12/1.01  fof(f45,plain,(
% 3.12/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(nnf_transformation,[],[f24])).
% 3.12/1.01  
% 3.12/1.01  fof(f46,plain,(
% 3.12/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(flattening,[],[f45])).
% 3.12/1.01  
% 3.12/1.01  fof(f47,plain,(
% 3.12/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(rectify,[],[f46])).
% 3.12/1.01  
% 3.12/1.01  fof(f48,plain,(
% 3.12/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.12/1.01    introduced(choice_axiom,[])).
% 3.12/1.01  
% 3.12/1.01  fof(f49,plain,(
% 3.12/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK0(X0,X1)) != sK0(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.12/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.12/1.01  
% 3.12/1.01  fof(f60,plain,(
% 3.12/1.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f49])).
% 3.12/1.01  
% 3.12/1.01  fof(f92,plain,(
% 3.12/1.01    ( ! [X0,X1] : (k6_partfun1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.12/1.01    inference(definition_unfolding,[],[f60,f75])).
% 3.12/1.01  
% 3.12/1.01  fof(f97,plain,(
% 3.12/1.01    ( ! [X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | r2_hidden(sK0(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.12/1.01    inference(equality_resolution,[],[f92])).
% 3.12/1.01  
% 3.12/1.01  fof(f1,axiom,(
% 3.12/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f20,plain,(
% 3.12/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.12/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 3.12/1.01  
% 3.12/1.01  fof(f22,plain,(
% 3.12/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.12/1.01    inference(ennf_transformation,[],[f20])).
% 3.12/1.01  
% 3.12/1.01  fof(f55,plain,(
% 3.12/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.12/1.01    inference(cnf_transformation,[],[f22])).
% 3.12/1.01  
% 3.12/1.01  fof(f2,axiom,(
% 3.12/1.01    v1_xboole_0(k1_xboole_0)),
% 3.12/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.01  
% 3.12/1.01  fof(f56,plain,(
% 3.12/1.01    v1_xboole_0(k1_xboole_0)),
% 3.12/1.01    inference(cnf_transformation,[],[f2])).
% 3.12/1.01  
% 3.12/1.01  cnf(c_25,negated_conjecture,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1926,plain,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_30,negated_conjecture,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.12/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1922,plain,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_9,plain,
% 3.12/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.12/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_18,plain,
% 3.12/1.01      ( ~ v2_funct_2(X0,X1)
% 3.12/1.01      | ~ v5_relat_1(X0,X1)
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | k2_relat_1(X0) = X1 ),
% 3.12/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_369,plain,
% 3.12/1.01      ( ~ v2_funct_2(X0,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | k2_relat_1(X0) = X1 ),
% 3.12/1.01      inference(resolution,[status(thm)],[c_9,c_18]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_8,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_381,plain,
% 3.12/1.01      ( ~ v2_funct_2(X0,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.12/1.01      | k2_relat_1(X0) = X1 ),
% 3.12/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_369,c_8]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1917,plain,
% 3.12/1.01      ( k2_relat_1(X0) = X1
% 3.12/1.01      | v2_funct_2(X0,X1) != iProver_top
% 3.12/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2914,plain,
% 3.12/1.01      ( k2_relat_1(sK2) = sK1 | v2_funct_2(sK2,sK1) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1922,c_1917]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_14,plain,
% 3.12/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.12/1.01      | v2_funct_2(X0,X2)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | ~ v1_funct_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_31,negated_conjecture,
% 3.12/1.01      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_475,plain,
% 3.12/1.01      ( v2_funct_2(X0,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | sK2 != X0
% 3.12/1.01      | sK1 != X1
% 3.12/1.01      | sK1 != X2 ),
% 3.12/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_476,plain,
% 3.12/1.01      ( v2_funct_2(sK2,sK1)
% 3.12/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | ~ v1_funct_1(sK2) ),
% 3.12/1.01      inference(unflattening,[status(thm)],[c_475]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_33,negated_conjecture,
% 3.12/1.01      ( v1_funct_1(sK2) ),
% 3.12/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_478,plain,
% 3.12/1.01      ( v2_funct_2(sK2,sK1) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_476,c_33,c_30]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_635,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | k2_relat_1(X0) = X2
% 3.12/1.01      | sK2 != X0
% 3.12/1.01      | sK1 != X2 ),
% 3.12/1.01      inference(resolution_lifted,[status(thm)],[c_381,c_478]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_636,plain,
% 3.12/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.12/1.01      | k2_relat_1(sK2) = sK1 ),
% 3.12/1.01      inference(unflattening,[status(thm)],[c_635]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_638,plain,
% 3.12/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | k2_relat_1(sK2) = sK1 ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_636]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3422,plain,
% 3.12/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_2914,c_30,c_638]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_11,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1932,plain,
% 3.12/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3013,plain,
% 3.12/1.01      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1922,c_1932]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3425,plain,
% 3.12/1.01      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_3422,c_3013]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_22,plain,
% 3.12/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.12/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.12/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.12/1.01      | ~ v2_funct_1(X2)
% 3.12/1.01      | ~ v1_funct_1(X2)
% 3.12/1.01      | ~ v1_funct_1(X3)
% 3.12/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.12/1.01      | k2_funct_1(X2) = X3
% 3.12/1.01      | k1_xboole_0 = X1
% 3.12/1.01      | k1_xboole_0 = X0 ),
% 3.12/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_21,plain,
% 3.12/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.12/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.12/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.12/1.01      | v2_funct_1(X2)
% 3.12/1.01      | ~ v1_funct_1(X2)
% 3.12/1.01      | ~ v1_funct_1(X3) ),
% 3.12/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_183,plain,
% 3.12/1.01      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.12/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.12/1.01      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.12/1.01      | ~ v1_funct_1(X2)
% 3.12/1.01      | ~ v1_funct_1(X3)
% 3.12/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.12/1.01      | k2_funct_1(X2) = X3
% 3.12/1.01      | k1_xboole_0 = X1
% 3.12/1.01      | k1_xboole_0 = X0 ),
% 3.12/1.01      inference(global_propositional_subsumption,[status(thm)],[c_22,c_21]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_184,plain,
% 3.12/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.12/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.12/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | ~ v1_funct_1(X3)
% 3.12/1.01      | ~ v1_funct_1(X2)
% 3.12/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.12/1.01      | k2_funct_1(X2) = X3
% 3.12/1.01      | k1_xboole_0 = X0
% 3.12/1.01      | k1_xboole_0 = X1 ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_183]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1919,plain,
% 3.12/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 3.12/1.01      | k2_funct_1(X2) = X3
% 3.12/1.01      | k1_xboole_0 = X0
% 3.12/1.01      | k1_xboole_0 = X1
% 3.12/1.01      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.12/1.01      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.12/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.12/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.12/1.01      | v1_funct_1(X2) != iProver_top
% 3.12/1.01      | v1_funct_1(X3) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3650,plain,
% 3.12/1.01      ( k2_funct_1(sK2) = X0
% 3.12/1.01      | sK1 = k1_xboole_0
% 3.12/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.12/1.01      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.12/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.12/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | v1_funct_1(X0) != iProver_top
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_3425,c_1919]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_34,plain,
% 3.12/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_32,negated_conjecture,
% 3.12/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_35,plain,
% 3.12/1.01      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_37,plain,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5193,plain,
% 3.12/1.01      ( v1_funct_1(X0) != iProver_top
% 3.12/1.01      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.12/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.12/1.01      | sK1 = k1_xboole_0
% 3.12/1.01      | k2_funct_1(sK2) = X0
% 3.12/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3650,c_34,c_35,c_37]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5194,plain,
% 3.12/1.01      ( k2_funct_1(sK2) = X0
% 3.12/1.01      | sK1 = k1_xboole_0
% 3.12/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.12/1.01      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.12/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_5193]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5205,plain,
% 3.12/1.01      ( k2_funct_1(sK2) = sK3
% 3.12/1.01      | sK1 = k1_xboole_0
% 3.12/1.01      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.12/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1926,c_5194]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_29,negated_conjecture,
% 3.12/1.01      ( v1_funct_1(sK3) ),
% 3.12/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_28,negated_conjecture,
% 3.12/1.01      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_26,negated_conjecture,
% 3.12/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.12/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5206,plain,
% 3.12/1.01      ( ~ v1_funct_2(sK3,sK1,sK1)
% 3.12/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | ~ v1_funct_1(sK3)
% 3.12/1.01      | k2_funct_1(sK2) = sK3
% 3.12/1.01      | sK1 = k1_xboole_0 ),
% 3.12/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5205]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5346,plain,
% 3.12/1.01      ( sK1 = k1_xboole_0 | k2_funct_1(sK2) = sK3 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_5205,c_38,c_39,c_41]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5347,plain,
% 3.12/1.01      ( k2_funct_1(sK2) = sK3 | sK1 = k1_xboole_0 ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_5346]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_24,negated_conjecture,
% 3.12/1.01      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1927,plain,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_19,plain,
% 3.12/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.12/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_494,plain,
% 3.12/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.12/1.01      | sK2 != X0
% 3.12/1.01      | sK1 != X1 ),
% 3.12/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_495,plain,
% 3.12/1.01      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.12/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | ~ v1_funct_1(sK2)
% 3.12/1.01      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.12/1.01      inference(unflattening,[status(thm)],[c_494]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_497,plain,
% 3.12/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_495,c_33,c_32,c_30]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1965,plain,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_1927,c_497]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5350,plain,
% 3.12/1.01      ( sK1 = k1_xboole_0 | r2_relset_1(sK1,sK1,sK3,sK3) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_5347,c_1965]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_41,plain,
% 3.12/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_12,plain,
% 3.12/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.12/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2171,plain,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.12/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2172,plain,
% 3.12/1.01      ( r2_relset_1(sK1,sK1,sK3,sK3) = iProver_top
% 3.12/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_2171]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5353,plain,
% 3.12/1.01      ( sK1 = k1_xboole_0 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_5350,c_41,c_2172]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5376,plain,
% 3.12/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK3,k2_funct_1(sK2)) != iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_5353,c_1965]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2,plain,
% 3.12/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.12/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_7,plain,
% 3.12/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2280,plain,
% 3.12/1.01      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_2,c_7]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2281,plain,
% 3.12/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_2280,c_2]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_23,plain,
% 3.12/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.12/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.12/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1928,plain,
% 3.12/1.01      ( k1_relset_1(X0,X0,X1) = X0
% 3.12/1.01      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.12/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.12/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3553,plain,
% 3.12/1.01      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.12/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1922,c_1928]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_10,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1933,plain,
% 3.12/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3022,plain,
% 3.12/1.01      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1922,c_1933]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3557,plain,
% 3.12/1.01      ( k1_relat_1(sK2) = sK1
% 3.12/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_3553,c_3022]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3655,plain,
% 3.12/1.01      ( k1_relat_1(sK2) = sK1 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3557,c_34,c_35]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4,plain,
% 3.12/1.01      ( r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 3.12/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1937,plain,
% 3.12/1.01      ( k6_partfun1(k1_relat_1(X0)) = X0
% 3.12/1.01      | r2_hidden(sK0(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 3.12/1.01      | v1_relat_1(X0) != iProver_top
% 3.12/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3660,plain,
% 3.12/1.01      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.12/1.01      | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_3655,c_1937]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3666,plain,
% 3.12/1.01      ( k6_partfun1(sK1) = sK2
% 3.12/1.01      | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_3660,c_3655]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2144,plain,
% 3.12/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | v1_relat_1(sK2) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2145,plain,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_2144]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5067,plain,
% 3.12/1.01      ( k6_partfun1(sK1) = sK2 | r2_hidden(sK0(sK1,sK2),sK1) = iProver_top ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3666,c_34,c_37,c_2145]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5359,plain,
% 3.12/1.01      ( k6_partfun1(k1_xboole_0) = sK2
% 3.12/1.01      | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_5353,c_5067]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5459,plain,
% 3.12/1.01      ( sK2 = k1_xboole_0
% 3.12/1.01      | r2_hidden(sK0(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_5359,c_2]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_0,plain,
% 3.12/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1,plain,
% 3.12/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_358,plain,
% 3.12/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.12/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_359,plain,
% 3.12/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.12/1.01      inference(unflattening,[status(thm)],[c_358]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1918,plain,
% 3.12/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5547,plain,
% 3.12/1.01      ( sK2 = k1_xboole_0 ),
% 3.12/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5459,c_1918]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1925,plain,
% 3.12/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3552,plain,
% 3.12/1.01      ( k1_relset_1(sK1,sK1,sK3) = sK1
% 3.12/1.01      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1925,c_1928]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3021,plain,
% 3.12/1.01      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1925,c_1933]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3564,plain,
% 3.12/1.01      ( k1_relat_1(sK3) = sK1
% 3.12/1.01      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_3552,c_3021]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_38,plain,
% 3.12/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_39,plain,
% 3.12/1.01      ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3819,plain,
% 3.12/1.01      ( k1_relat_1(sK3) = sK1 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3564,c_38,c_39]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3824,plain,
% 3.12/1.01      ( k6_partfun1(k1_relat_1(sK3)) = sK3
% 3.12/1.01      | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
% 3.12/1.01      | v1_relat_1(sK3) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_3819,c_1937]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3830,plain,
% 3.12/1.01      ( k6_partfun1(sK1) = sK3
% 3.12/1.01      | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top
% 3.12/1.01      | v1_relat_1(sK3) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_3824,c_3819]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2141,plain,
% 3.12/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.12/1.01      | v1_relat_1(sK3) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2142,plain,
% 3.12/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.12/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_2141]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5076,plain,
% 3.12/1.01      ( k6_partfun1(sK1) = sK3 | r2_hidden(sK0(sK1,sK3),sK1) = iProver_top ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3830,c_38,c_41,c_2142]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5358,plain,
% 3.12/1.01      ( k6_partfun1(k1_xboole_0) = sK3
% 3.12/1.01      | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_5353,c_5076]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5464,plain,
% 3.12/1.01      ( sK3 = k1_xboole_0
% 3.12/1.01      | r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0) = iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_5358,c_2]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5646,plain,
% 3.12/1.01      ( sK3 = k1_xboole_0 ),
% 3.12/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5464,c_1918]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6138,plain,
% 3.12/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_5376,c_2281,c_5547,c_5646]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5380,plain,
% 3.12/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.12/1.01      inference(demodulation,[status(thm)],[c_5353,c_1925]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5907,plain,
% 3.12/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_5380,c_5646]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1931,plain,
% 3.12/1.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.12/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5914,plain,
% 3.12/1.01      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_5907,c_1931]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6140,plain,
% 3.12/1.01      ( $false ),
% 3.12/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6138,c_5914]) ).
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/1.01  
% 3.12/1.01  ------                               Statistics
% 3.12/1.01  
% 3.12/1.01  ------ General
% 3.12/1.01  
% 3.12/1.01  abstr_ref_over_cycles:                  0
% 3.12/1.01  abstr_ref_under_cycles:                 0
% 3.12/1.01  gc_basic_clause_elim:                   0
% 3.12/1.01  forced_gc_time:                         0
% 3.12/1.01  parsing_time:                           0.013
% 3.12/1.01  unif_index_cands_time:                  0.
% 3.12/1.01  unif_index_add_time:                    0.
% 3.12/1.01  orderings_time:                         0.
% 3.12/1.01  out_proof_time:                         0.009
% 3.12/1.01  total_time:                             0.245
% 3.12/1.01  num_of_symbols:                         58
% 3.12/1.01  num_of_terms:                           6818
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing
% 3.12/1.01  
% 3.12/1.01  num_of_splits:                          0
% 3.12/1.01  num_of_split_atoms:                     0
% 3.12/1.01  num_of_reused_defs:                     0
% 3.12/1.01  num_eq_ax_congr_red:                    27
% 3.12/1.01  num_of_sem_filtered_clauses:            3
% 3.12/1.01  num_of_subtypes:                        0
% 3.12/1.01  monotx_restored_types:                  0
% 3.12/1.01  sat_num_of_epr_types:                   0
% 3.12/1.01  sat_num_of_non_cyclic_types:            0
% 3.12/1.01  sat_guarded_non_collapsed_types:        0
% 3.12/1.01  num_pure_diseq_elim:                    0
% 3.12/1.01  simp_replaced_by:                       0
% 3.12/1.01  res_preprocessed:                       157
% 3.12/1.01  prep_upred:                             0
% 3.12/1.01  prep_unflattend:                        77
% 3.12/1.01  smt_new_axioms:                         0
% 3.12/1.01  pred_elim_cands:                        7
% 3.12/1.01  pred_elim:                              3
% 3.12/1.01  pred_elim_cl:                           2
% 3.12/1.01  pred_elim_cycles:                       11
% 3.12/1.01  merged_defs:                            0
% 3.12/1.01  merged_defs_ncl:                        0
% 3.12/1.01  bin_hyper_res:                          0
% 3.12/1.01  prep_cycles:                            4
% 3.12/1.01  pred_elim_time:                         0.021
% 3.12/1.01  splitting_time:                         0.
% 3.12/1.01  sem_filter_time:                        0.
% 3.12/1.01  monotx_time:                            0.001
% 3.12/1.01  subtype_inf_time:                       0.
% 3.12/1.01  
% 3.12/1.01  ------ Problem properties
% 3.12/1.01  
% 3.12/1.01  clauses:                                29
% 3.12/1.01  conjectures:                            8
% 3.12/1.01  epr:                                    7
% 3.12/1.01  horn:                                   27
% 3.12/1.01  ground:                                 13
% 3.12/1.01  unary:                                  15
% 3.12/1.01  binary:                                 5
% 3.12/1.01  lits:                                   70
% 3.12/1.01  lits_eq:                                18
% 3.12/1.01  fd_pure:                                0
% 3.12/1.01  fd_pseudo:                              0
% 3.12/1.01  fd_cond:                                0
% 3.12/1.01  fd_pseudo_cond:                         3
% 3.12/1.01  ac_symbols:                             0
% 3.12/1.01  
% 3.12/1.01  ------ Propositional Solver
% 3.12/1.01  
% 3.12/1.01  prop_solver_calls:                      26
% 3.12/1.01  prop_fast_solver_calls:                 1296
% 3.12/1.01  smt_solver_calls:                       0
% 3.12/1.01  smt_fast_solver_calls:                  0
% 3.12/1.01  prop_num_of_clauses:                    2154
% 3.12/1.01  prop_preprocess_simplified:             6560
% 3.12/1.01  prop_fo_subsumed:                       41
% 3.12/1.01  prop_solver_time:                       0.
% 3.12/1.01  smt_solver_time:                        0.
% 3.12/1.01  smt_fast_solver_time:                   0.
% 3.12/1.01  prop_fast_solver_time:                  0.
% 3.12/1.01  prop_unsat_core_time:                   0.
% 3.12/1.01  
% 3.12/1.01  ------ QBF
% 3.12/1.01  
% 3.12/1.01  qbf_q_res:                              0
% 3.12/1.01  qbf_num_tautologies:                    0
% 3.12/1.01  qbf_prep_cycles:                        0
% 3.12/1.01  
% 3.12/1.01  ------ BMC1
% 3.12/1.01  
% 3.12/1.01  bmc1_current_bound:                     -1
% 3.12/1.01  bmc1_last_solved_bound:                 -1
% 3.12/1.01  bmc1_unsat_core_size:                   -1
% 3.12/1.01  bmc1_unsat_core_parents_size:           -1
% 3.12/1.01  bmc1_merge_next_fun:                    0
% 3.12/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.12/1.01  
% 3.12/1.01  ------ Instantiation
% 3.12/1.01  
% 3.12/1.01  inst_num_of_clauses:                    634
% 3.12/1.01  inst_num_in_passive:                    56
% 3.12/1.01  inst_num_in_active:                     340
% 3.12/1.01  inst_num_in_unprocessed:                238
% 3.12/1.01  inst_num_of_loops:                      380
% 3.12/1.01  inst_num_of_learning_restarts:          0
% 3.12/1.01  inst_num_moves_active_passive:          37
% 3.12/1.01  inst_lit_activity:                      0
% 3.12/1.01  inst_lit_activity_moves:                0
% 3.12/1.01  inst_num_tautologies:                   0
% 3.12/1.01  inst_num_prop_implied:                  0
% 3.12/1.01  inst_num_existing_simplified:           0
% 3.12/1.01  inst_num_eq_res_simplified:             0
% 3.12/1.01  inst_num_child_elim:                    0
% 3.12/1.01  inst_num_of_dismatching_blockings:      240
% 3.12/1.01  inst_num_of_non_proper_insts:           606
% 3.12/1.01  inst_num_of_duplicates:                 0
% 3.12/1.01  inst_inst_num_from_inst_to_res:         0
% 3.12/1.01  inst_dismatching_checking_time:         0.
% 3.12/1.01  
% 3.12/1.01  ------ Resolution
% 3.12/1.01  
% 3.12/1.01  res_num_of_clauses:                     0
% 3.12/1.01  res_num_in_passive:                     0
% 3.12/1.01  res_num_in_active:                      0
% 3.12/1.01  res_num_of_loops:                       161
% 3.12/1.01  res_forward_subset_subsumed:            27
% 3.12/1.01  res_backward_subset_subsumed:           0
% 3.12/1.01  res_forward_subsumed:                   0
% 3.12/1.01  res_backward_subsumed:                  0
% 3.12/1.01  res_forward_subsumption_resolution:     2
% 3.12/1.01  res_backward_subsumption_resolution:    0
% 3.12/1.01  res_clause_to_clause_subsumption:       145
% 3.12/1.01  res_orphan_elimination:                 0
% 3.12/1.01  res_tautology_del:                      24
% 3.12/1.01  res_num_eq_res_simplified:              0
% 3.12/1.01  res_num_sel_changes:                    0
% 3.12/1.01  res_moves_from_active_to_pass:          0
% 3.12/1.01  
% 3.12/1.01  ------ Superposition
% 3.12/1.01  
% 3.12/1.01  sup_time_total:                         0.
% 3.12/1.01  sup_time_generating:                    0.
% 3.12/1.01  sup_time_sim_full:                      0.
% 3.12/1.01  sup_time_sim_immed:                     0.
% 3.12/1.01  
% 3.12/1.01  sup_num_of_clauses:                     59
% 3.12/1.01  sup_num_in_active:                      35
% 3.12/1.01  sup_num_in_passive:                     24
% 3.12/1.01  sup_num_of_loops:                       74
% 3.12/1.01  sup_fw_superposition:                   23
% 3.12/1.01  sup_bw_superposition:                   25
% 3.12/1.01  sup_immediate_simplified:               20
% 3.12/1.01  sup_given_eliminated:                   0
% 3.12/1.01  comparisons_done:                       0
% 3.12/1.01  comparisons_avoided:                    6
% 3.12/1.01  
% 3.12/1.01  ------ Simplifications
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  sim_fw_subset_subsumed:                 2
% 3.12/1.01  sim_bw_subset_subsumed:                 2
% 3.12/1.01  sim_fw_subsumed:                        2
% 3.12/1.01  sim_bw_subsumed:                        0
% 3.12/1.01  sim_fw_subsumption_res:                 3
% 3.12/1.01  sim_bw_subsumption_res:                 0
% 3.12/1.01  sim_tautology_del:                      0
% 3.12/1.01  sim_eq_tautology_del:                   8
% 3.12/1.01  sim_eq_res_simp:                        0
% 3.12/1.01  sim_fw_demodulated:                     2
% 3.12/1.01  sim_bw_demodulated:                     40
% 3.12/1.01  sim_light_normalised:                   32
% 3.12/1.01  sim_joinable_taut:                      0
% 3.12/1.01  sim_joinable_simp:                      0
% 3.12/1.01  sim_ac_normalised:                      0
% 3.12/1.01  sim_smt_subsumption:                    0
% 3.12/1.01  
%------------------------------------------------------------------------------
