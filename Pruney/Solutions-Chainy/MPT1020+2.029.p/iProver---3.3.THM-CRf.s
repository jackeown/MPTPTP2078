%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:10 EST 2020

% Result     : Theorem 51.42s
% Output     : CNFRefutation 51.42s
% Verified   : 
% Statistics : Number of formulae       :  237 (7579 expanded)
%              Number of clauses        :  153 (2291 expanded)
%              Number of leaves         :   20 (1837 expanded)
%              Depth                    :   30
%              Number of atoms          :  823 (54308 expanded)
%              Number of equality atoms :  327 (4286 expanded)
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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f50,f49])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1659,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2206,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1662,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1662])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1667,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
    | ~ v1_funct_1(X3_51)
    | ~ v1_funct_1(X0_51)
    | k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51) = k5_relat_1(X3_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2198,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X4_51,X5_51) = k5_relat_1(X4_51,X5_51)
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_3860,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_2198])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4300,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_38])).

cnf(c_4301,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4300])).

cnf(c_4307,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_4301])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4088,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_4595,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4307,c_33,c_30,c_29,c_26,c_4088])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1673,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2192,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1673])).

cnf(c_3361,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2206,c_2192])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_178,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_22])).

cnf(c_179,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_1656,plain,
    ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
    | ~ v1_funct_2(X3_51,X1_51,X0_51)
    | ~ v1_funct_2(X2_51,X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X2_51)
    | ~ v1_funct_1(X3_51)
    | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X0_51
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_2209,plain,
    ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
    | k2_funct_1(X2_51) = X3_51
    | k1_xboole_0 = X0_51
    | k1_xboole_0 = X1_51
    | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
    | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_5096,plain,
    ( k2_funct_1(sK1) = X0_51
    | k2_relat_1(sK1) != sK0
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_2209])).

cnf(c_34,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_490,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_491,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_492,plain,
    ( v2_funct_2(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_344,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_15])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_356,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_344,c_6])).

cnf(c_1655,plain,
    ( ~ v2_funct_2(X0_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | k2_relat_1(X0_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_2210,plain,
    ( k2_relat_1(X0_51) = X1_51
    | v2_funct_2(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_5623,plain,
    ( k2_relat_1(sK1) = sK0
    | v2_funct_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_2210])).

cnf(c_9682,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0
    | k2_funct_1(sK1) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_34,c_35,c_37,c_492,c_5623])).

cnf(c_9683,plain,
    ( k2_funct_1(sK1) = X0_51
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(X0_51,sK0,sK0) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_9682])).

cnf(c_9688,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4595,c_9683])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1663,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2202,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_4597,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4595,c_2202])).

cnf(c_4598,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4597])).

cnf(c_9690,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9688])).

cnf(c_9693,plain,
    ( k2_funct_1(sK1) = sK2
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9688,c_29,c_28,c_26,c_4598,c_9690])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1664,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2201,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_510,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_33,c_32,c_30])).

cnf(c_1648,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_2216,plain,
    ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2201,c_1648])).

cnf(c_9695,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9693,c_2216])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1672,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2278,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_2279,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2278])).

cnf(c_9769,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9695,c_41,c_2279])).

cnf(c_5798,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5623,c_34,c_37,c_492])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1678,plain,
    ( ~ v1_relat_1(X0_51)
    | k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2188,plain,
    ( k2_relat_1(X0_51) != k1_xboole_0
    | k1_xboole_0 = X0_51
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1678])).

cnf(c_5802,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5798,c_2188])).

cnf(c_1674,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2191,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1674])).

cnf(c_3153,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_2191])).

cnf(c_5987,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5802,c_3153])).

cnf(c_5988,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5987])).

cnf(c_9807,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9769,c_5988])).

cnf(c_9875,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9807])).

cnf(c_5622,plain,
    ( k2_relat_1(sK2) = sK0
    | v2_funct_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_2210])).

cnf(c_27,negated_conjecture,
    ( v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_468,plain,
    ( v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_469,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_470,plain,
    ( v2_funct_2(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_5790,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5622,c_38,c_41,c_470])).

cnf(c_5794,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5790,c_2188])).

cnf(c_3144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_3146,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_5796,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5794])).

cnf(c_5984,plain,
    ( sK0 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5794,c_26,c_3146,c_5796])).

cnf(c_5985,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5984])).

cnf(c_9808,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9769,c_5985])).

cnf(c_9850,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9808])).

cnf(c_9828,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9769,c_4597])).

cnf(c_4,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1676,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9847,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9828,c_1676])).

cnf(c_9862,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9850,c_9847])).

cnf(c_9879,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9875,c_9862])).

cnf(c_4306,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_4301])).

cnf(c_4321,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4306,c_38])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1670,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
    | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X3_51)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2195,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) = iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_4324,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4321,c_2195])).

cnf(c_5419,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4324,c_38,c_41])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1671,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X2_51,X3_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | X3_51 = X2_51 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2194,plain,
    ( X0_51 = X1_51
    | r2_relset_1(X2_51,X3_51,X1_51,X0_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1671])).

cnf(c_5429,plain,
    ( k5_relat_1(sK2,sK2) = X0_51
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK2),X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5419,c_2194])).

cnf(c_9793,plain,
    ( k5_relat_1(sK2,sK2) = X0_51
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,sK2),X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9769,c_5429])).

cnf(c_9908,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = X0_51
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9793,c_9850])).

cnf(c_23321,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9879,c_9908])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1668,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2197,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_2797,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_2197])).

cnf(c_134487,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23321,c_2797])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1675,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | ~ v2_funct_1(X1_51)
    | ~ v1_relat_1(X1_51)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
    | k2_funct_1(X1_51) = X0_51
    | k1_relat_1(X1_51) != k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2190,plain,
    ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
    | k2_funct_1(X1_51) = X0_51
    | k1_relat_1(X1_51) != k2_relat_1(X0_51)
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1675])).

cnf(c_135524,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_134487,c_2190])).

cnf(c_1,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1679,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1680,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_135525,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_135524,c_1676,c_1679,c_1680])).

cnf(c_135526,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_135525])).

cnf(c_3155,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_2191])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( v2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_29,c_26])).

cnf(c_1653,plain,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_460])).

cnf(c_2212,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_13682,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9850,c_2212])).

cnf(c_1660,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2205,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_13683,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9850,c_2205])).

cnf(c_135687,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_135526,c_3155,c_13682,c_13683])).

cnf(c_9838,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9769,c_2216])).

cnf(c_9870,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9850,c_9838])).

cnf(c_9881,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9875,c_9870])).

cnf(c_135689,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_135687,c_9881])).

cnf(c_2193,plain,
    ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1672])).

cnf(c_3796,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_2193])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135689,c_3796])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 51.42/7.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.42/7.03  
% 51.42/7.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.42/7.03  
% 51.42/7.03  ------  iProver source info
% 51.42/7.03  
% 51.42/7.03  git: date: 2020-06-30 10:37:57 +0100
% 51.42/7.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.42/7.03  git: non_committed_changes: false
% 51.42/7.03  git: last_make_outside_of_git: false
% 51.42/7.03  
% 51.42/7.03  ------ 
% 51.42/7.03  
% 51.42/7.03  ------ Input Options
% 51.42/7.03  
% 51.42/7.03  --out_options                           all
% 51.42/7.03  --tptp_safe_out                         true
% 51.42/7.03  --problem_path                          ""
% 51.42/7.03  --include_path                          ""
% 51.42/7.03  --clausifier                            res/vclausify_rel
% 51.42/7.03  --clausifier_options                    ""
% 51.42/7.03  --stdin                                 false
% 51.42/7.03  --stats_out                             all
% 51.42/7.03  
% 51.42/7.03  ------ General Options
% 51.42/7.03  
% 51.42/7.03  --fof                                   false
% 51.42/7.03  --time_out_real                         305.
% 51.42/7.03  --time_out_virtual                      -1.
% 51.42/7.03  --symbol_type_check                     false
% 51.42/7.03  --clausify_out                          false
% 51.42/7.03  --sig_cnt_out                           false
% 51.42/7.03  --trig_cnt_out                          false
% 51.42/7.03  --trig_cnt_out_tolerance                1.
% 51.42/7.03  --trig_cnt_out_sk_spl                   false
% 51.42/7.03  --abstr_cl_out                          false
% 51.42/7.03  
% 51.42/7.03  ------ Global Options
% 51.42/7.03  
% 51.42/7.03  --schedule                              default
% 51.42/7.03  --add_important_lit                     false
% 51.42/7.03  --prop_solver_per_cl                    1000
% 51.42/7.03  --min_unsat_core                        false
% 51.42/7.03  --soft_assumptions                      false
% 51.42/7.03  --soft_lemma_size                       3
% 51.42/7.03  --prop_impl_unit_size                   0
% 51.42/7.03  --prop_impl_unit                        []
% 51.42/7.03  --share_sel_clauses                     true
% 51.42/7.03  --reset_solvers                         false
% 51.42/7.03  --bc_imp_inh                            [conj_cone]
% 51.42/7.03  --conj_cone_tolerance                   3.
% 51.42/7.03  --extra_neg_conj                        none
% 51.42/7.03  --large_theory_mode                     true
% 51.42/7.03  --prolific_symb_bound                   200
% 51.42/7.03  --lt_threshold                          2000
% 51.42/7.03  --clause_weak_htbl                      true
% 51.42/7.03  --gc_record_bc_elim                     false
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing Options
% 51.42/7.03  
% 51.42/7.03  --preprocessing_flag                    true
% 51.42/7.03  --time_out_prep_mult                    0.1
% 51.42/7.03  --splitting_mode                        input
% 51.42/7.03  --splitting_grd                         true
% 51.42/7.03  --splitting_cvd                         false
% 51.42/7.03  --splitting_cvd_svl                     false
% 51.42/7.03  --splitting_nvd                         32
% 51.42/7.03  --sub_typing                            true
% 51.42/7.03  --prep_gs_sim                           true
% 51.42/7.03  --prep_unflatten                        true
% 51.42/7.03  --prep_res_sim                          true
% 51.42/7.03  --prep_upred                            true
% 51.42/7.03  --prep_sem_filter                       exhaustive
% 51.42/7.03  --prep_sem_filter_out                   false
% 51.42/7.03  --pred_elim                             true
% 51.42/7.03  --res_sim_input                         true
% 51.42/7.03  --eq_ax_congr_red                       true
% 51.42/7.03  --pure_diseq_elim                       true
% 51.42/7.03  --brand_transform                       false
% 51.42/7.03  --non_eq_to_eq                          false
% 51.42/7.03  --prep_def_merge                        true
% 51.42/7.03  --prep_def_merge_prop_impl              false
% 51.42/7.03  --prep_def_merge_mbd                    true
% 51.42/7.03  --prep_def_merge_tr_red                 false
% 51.42/7.03  --prep_def_merge_tr_cl                  false
% 51.42/7.03  --smt_preprocessing                     true
% 51.42/7.03  --smt_ac_axioms                         fast
% 51.42/7.03  --preprocessed_out                      false
% 51.42/7.03  --preprocessed_stats                    false
% 51.42/7.03  
% 51.42/7.03  ------ Abstraction refinement Options
% 51.42/7.03  
% 51.42/7.03  --abstr_ref                             []
% 51.42/7.03  --abstr_ref_prep                        false
% 51.42/7.03  --abstr_ref_until_sat                   false
% 51.42/7.03  --abstr_ref_sig_restrict                funpre
% 51.42/7.03  --abstr_ref_af_restrict_to_split_sk     false
% 51.42/7.03  --abstr_ref_under                       []
% 51.42/7.03  
% 51.42/7.03  ------ SAT Options
% 51.42/7.03  
% 51.42/7.03  --sat_mode                              false
% 51.42/7.03  --sat_fm_restart_options                ""
% 51.42/7.03  --sat_gr_def                            false
% 51.42/7.03  --sat_epr_types                         true
% 51.42/7.03  --sat_non_cyclic_types                  false
% 51.42/7.03  --sat_finite_models                     false
% 51.42/7.03  --sat_fm_lemmas                         false
% 51.42/7.03  --sat_fm_prep                           false
% 51.42/7.03  --sat_fm_uc_incr                        true
% 51.42/7.03  --sat_out_model                         small
% 51.42/7.03  --sat_out_clauses                       false
% 51.42/7.03  
% 51.42/7.03  ------ QBF Options
% 51.42/7.03  
% 51.42/7.03  --qbf_mode                              false
% 51.42/7.03  --qbf_elim_univ                         false
% 51.42/7.03  --qbf_dom_inst                          none
% 51.42/7.03  --qbf_dom_pre_inst                      false
% 51.42/7.03  --qbf_sk_in                             false
% 51.42/7.03  --qbf_pred_elim                         true
% 51.42/7.03  --qbf_split                             512
% 51.42/7.03  
% 51.42/7.03  ------ BMC1 Options
% 51.42/7.03  
% 51.42/7.03  --bmc1_incremental                      false
% 51.42/7.03  --bmc1_axioms                           reachable_all
% 51.42/7.03  --bmc1_min_bound                        0
% 51.42/7.03  --bmc1_max_bound                        -1
% 51.42/7.03  --bmc1_max_bound_default                -1
% 51.42/7.03  --bmc1_symbol_reachability              true
% 51.42/7.03  --bmc1_property_lemmas                  false
% 51.42/7.03  --bmc1_k_induction                      false
% 51.42/7.03  --bmc1_non_equiv_states                 false
% 51.42/7.03  --bmc1_deadlock                         false
% 51.42/7.03  --bmc1_ucm                              false
% 51.42/7.03  --bmc1_add_unsat_core                   none
% 51.42/7.03  --bmc1_unsat_core_children              false
% 51.42/7.03  --bmc1_unsat_core_extrapolate_axioms    false
% 51.42/7.03  --bmc1_out_stat                         full
% 51.42/7.03  --bmc1_ground_init                      false
% 51.42/7.03  --bmc1_pre_inst_next_state              false
% 51.42/7.03  --bmc1_pre_inst_state                   false
% 51.42/7.03  --bmc1_pre_inst_reach_state             false
% 51.42/7.03  --bmc1_out_unsat_core                   false
% 51.42/7.03  --bmc1_aig_witness_out                  false
% 51.42/7.03  --bmc1_verbose                          false
% 51.42/7.03  --bmc1_dump_clauses_tptp                false
% 51.42/7.03  --bmc1_dump_unsat_core_tptp             false
% 51.42/7.03  --bmc1_dump_file                        -
% 51.42/7.03  --bmc1_ucm_expand_uc_limit              128
% 51.42/7.03  --bmc1_ucm_n_expand_iterations          6
% 51.42/7.03  --bmc1_ucm_extend_mode                  1
% 51.42/7.03  --bmc1_ucm_init_mode                    2
% 51.42/7.03  --bmc1_ucm_cone_mode                    none
% 51.42/7.03  --bmc1_ucm_reduced_relation_type        0
% 51.42/7.03  --bmc1_ucm_relax_model                  4
% 51.42/7.03  --bmc1_ucm_full_tr_after_sat            true
% 51.42/7.03  --bmc1_ucm_expand_neg_assumptions       false
% 51.42/7.03  --bmc1_ucm_layered_model                none
% 51.42/7.03  --bmc1_ucm_max_lemma_size               10
% 51.42/7.03  
% 51.42/7.03  ------ AIG Options
% 51.42/7.03  
% 51.42/7.03  --aig_mode                              false
% 51.42/7.03  
% 51.42/7.03  ------ Instantiation Options
% 51.42/7.03  
% 51.42/7.03  --instantiation_flag                    true
% 51.42/7.03  --inst_sos_flag                         true
% 51.42/7.03  --inst_sos_phase                        true
% 51.42/7.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.42/7.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.42/7.03  --inst_lit_sel_side                     num_symb
% 51.42/7.03  --inst_solver_per_active                1400
% 51.42/7.03  --inst_solver_calls_frac                1.
% 51.42/7.03  --inst_passive_queue_type               priority_queues
% 51.42/7.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.42/7.03  --inst_passive_queues_freq              [25;2]
% 51.42/7.03  --inst_dismatching                      true
% 51.42/7.03  --inst_eager_unprocessed_to_passive     true
% 51.42/7.03  --inst_prop_sim_given                   true
% 51.42/7.03  --inst_prop_sim_new                     false
% 51.42/7.03  --inst_subs_new                         false
% 51.42/7.03  --inst_eq_res_simp                      false
% 51.42/7.03  --inst_subs_given                       false
% 51.42/7.03  --inst_orphan_elimination               true
% 51.42/7.03  --inst_learning_loop_flag               true
% 51.42/7.03  --inst_learning_start                   3000
% 51.42/7.03  --inst_learning_factor                  2
% 51.42/7.03  --inst_start_prop_sim_after_learn       3
% 51.42/7.03  --inst_sel_renew                        solver
% 51.42/7.03  --inst_lit_activity_flag                true
% 51.42/7.03  --inst_restr_to_given                   false
% 51.42/7.03  --inst_activity_threshold               500
% 51.42/7.03  --inst_out_proof                        true
% 51.42/7.03  
% 51.42/7.03  ------ Resolution Options
% 51.42/7.03  
% 51.42/7.03  --resolution_flag                       true
% 51.42/7.03  --res_lit_sel                           adaptive
% 51.42/7.03  --res_lit_sel_side                      none
% 51.42/7.03  --res_ordering                          kbo
% 51.42/7.03  --res_to_prop_solver                    active
% 51.42/7.03  --res_prop_simpl_new                    false
% 51.42/7.03  --res_prop_simpl_given                  true
% 51.42/7.03  --res_passive_queue_type                priority_queues
% 51.42/7.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.42/7.03  --res_passive_queues_freq               [15;5]
% 51.42/7.03  --res_forward_subs                      full
% 51.42/7.03  --res_backward_subs                     full
% 51.42/7.03  --res_forward_subs_resolution           true
% 51.42/7.03  --res_backward_subs_resolution          true
% 51.42/7.03  --res_orphan_elimination                true
% 51.42/7.03  --res_time_limit                        2.
% 51.42/7.03  --res_out_proof                         true
% 51.42/7.03  
% 51.42/7.03  ------ Superposition Options
% 51.42/7.03  
% 51.42/7.03  --superposition_flag                    true
% 51.42/7.03  --sup_passive_queue_type                priority_queues
% 51.42/7.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.42/7.03  --sup_passive_queues_freq               [8;1;4]
% 51.42/7.03  --demod_completeness_check              fast
% 51.42/7.03  --demod_use_ground                      true
% 51.42/7.03  --sup_to_prop_solver                    passive
% 51.42/7.03  --sup_prop_simpl_new                    true
% 51.42/7.03  --sup_prop_simpl_given                  true
% 51.42/7.03  --sup_fun_splitting                     true
% 51.42/7.03  --sup_smt_interval                      50000
% 51.42/7.03  
% 51.42/7.03  ------ Superposition Simplification Setup
% 51.42/7.03  
% 51.42/7.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.42/7.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.42/7.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.42/7.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.42/7.03  --sup_full_triv                         [TrivRules;PropSubs]
% 51.42/7.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.42/7.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.42/7.03  --sup_immed_triv                        [TrivRules]
% 51.42/7.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_immed_bw_main                     []
% 51.42/7.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.42/7.03  --sup_input_triv                        [Unflattening;TrivRules]
% 51.42/7.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_input_bw                          []
% 51.42/7.03  
% 51.42/7.03  ------ Combination Options
% 51.42/7.03  
% 51.42/7.03  --comb_res_mult                         3
% 51.42/7.03  --comb_sup_mult                         2
% 51.42/7.03  --comb_inst_mult                        10
% 51.42/7.03  
% 51.42/7.03  ------ Debug Options
% 51.42/7.03  
% 51.42/7.03  --dbg_backtrace                         false
% 51.42/7.03  --dbg_dump_prop_clauses                 false
% 51.42/7.03  --dbg_dump_prop_clauses_file            -
% 51.42/7.03  --dbg_out_stat                          false
% 51.42/7.03  ------ Parsing...
% 51.42/7.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.42/7.03  ------ Proving...
% 51.42/7.03  ------ Problem Properties 
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  clauses                                 33
% 51.42/7.03  conjectures                             8
% 51.42/7.03  EPR                                     8
% 51.42/7.03  Horn                                    32
% 51.42/7.03  unary                                   18
% 51.42/7.03  binary                                  4
% 51.42/7.03  lits                                    89
% 51.42/7.03  lits eq                                 20
% 51.42/7.03  fd_pure                                 0
% 51.42/7.03  fd_pseudo                               0
% 51.42/7.03  fd_cond                                 2
% 51.42/7.03  fd_pseudo_cond                          4
% 51.42/7.03  AC symbols                              0
% 51.42/7.03  
% 51.42/7.03  ------ Schedule dynamic 5 is on 
% 51.42/7.03  
% 51.42/7.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  ------ 
% 51.42/7.03  Current options:
% 51.42/7.03  ------ 
% 51.42/7.03  
% 51.42/7.03  ------ Input Options
% 51.42/7.03  
% 51.42/7.03  --out_options                           all
% 51.42/7.03  --tptp_safe_out                         true
% 51.42/7.03  --problem_path                          ""
% 51.42/7.03  --include_path                          ""
% 51.42/7.03  --clausifier                            res/vclausify_rel
% 51.42/7.03  --clausifier_options                    ""
% 51.42/7.03  --stdin                                 false
% 51.42/7.03  --stats_out                             all
% 51.42/7.03  
% 51.42/7.03  ------ General Options
% 51.42/7.03  
% 51.42/7.03  --fof                                   false
% 51.42/7.03  --time_out_real                         305.
% 51.42/7.03  --time_out_virtual                      -1.
% 51.42/7.03  --symbol_type_check                     false
% 51.42/7.03  --clausify_out                          false
% 51.42/7.03  --sig_cnt_out                           false
% 51.42/7.03  --trig_cnt_out                          false
% 51.42/7.03  --trig_cnt_out_tolerance                1.
% 51.42/7.03  --trig_cnt_out_sk_spl                   false
% 51.42/7.03  --abstr_cl_out                          false
% 51.42/7.03  
% 51.42/7.03  ------ Global Options
% 51.42/7.03  
% 51.42/7.03  --schedule                              default
% 51.42/7.03  --add_important_lit                     false
% 51.42/7.03  --prop_solver_per_cl                    1000
% 51.42/7.03  --min_unsat_core                        false
% 51.42/7.03  --soft_assumptions                      false
% 51.42/7.03  --soft_lemma_size                       3
% 51.42/7.03  --prop_impl_unit_size                   0
% 51.42/7.03  --prop_impl_unit                        []
% 51.42/7.03  --share_sel_clauses                     true
% 51.42/7.03  --reset_solvers                         false
% 51.42/7.03  --bc_imp_inh                            [conj_cone]
% 51.42/7.03  --conj_cone_tolerance                   3.
% 51.42/7.03  --extra_neg_conj                        none
% 51.42/7.03  --large_theory_mode                     true
% 51.42/7.03  --prolific_symb_bound                   200
% 51.42/7.03  --lt_threshold                          2000
% 51.42/7.03  --clause_weak_htbl                      true
% 51.42/7.03  --gc_record_bc_elim                     false
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing Options
% 51.42/7.03  
% 51.42/7.03  --preprocessing_flag                    true
% 51.42/7.03  --time_out_prep_mult                    0.1
% 51.42/7.03  --splitting_mode                        input
% 51.42/7.03  --splitting_grd                         true
% 51.42/7.03  --splitting_cvd                         false
% 51.42/7.03  --splitting_cvd_svl                     false
% 51.42/7.03  --splitting_nvd                         32
% 51.42/7.03  --sub_typing                            true
% 51.42/7.03  --prep_gs_sim                           true
% 51.42/7.03  --prep_unflatten                        true
% 51.42/7.03  --prep_res_sim                          true
% 51.42/7.03  --prep_upred                            true
% 51.42/7.03  --prep_sem_filter                       exhaustive
% 51.42/7.03  --prep_sem_filter_out                   false
% 51.42/7.03  --pred_elim                             true
% 51.42/7.03  --res_sim_input                         true
% 51.42/7.03  --eq_ax_congr_red                       true
% 51.42/7.03  --pure_diseq_elim                       true
% 51.42/7.03  --brand_transform                       false
% 51.42/7.03  --non_eq_to_eq                          false
% 51.42/7.03  --prep_def_merge                        true
% 51.42/7.03  --prep_def_merge_prop_impl              false
% 51.42/7.03  --prep_def_merge_mbd                    true
% 51.42/7.03  --prep_def_merge_tr_red                 false
% 51.42/7.03  --prep_def_merge_tr_cl                  false
% 51.42/7.03  --smt_preprocessing                     true
% 51.42/7.03  --smt_ac_axioms                         fast
% 51.42/7.03  --preprocessed_out                      false
% 51.42/7.03  --preprocessed_stats                    false
% 51.42/7.03  
% 51.42/7.03  ------ Abstraction refinement Options
% 51.42/7.03  
% 51.42/7.03  --abstr_ref                             []
% 51.42/7.03  --abstr_ref_prep                        false
% 51.42/7.03  --abstr_ref_until_sat                   false
% 51.42/7.03  --abstr_ref_sig_restrict                funpre
% 51.42/7.03  --abstr_ref_af_restrict_to_split_sk     false
% 51.42/7.03  --abstr_ref_under                       []
% 51.42/7.03  
% 51.42/7.03  ------ SAT Options
% 51.42/7.03  
% 51.42/7.03  --sat_mode                              false
% 51.42/7.03  --sat_fm_restart_options                ""
% 51.42/7.03  --sat_gr_def                            false
% 51.42/7.03  --sat_epr_types                         true
% 51.42/7.03  --sat_non_cyclic_types                  false
% 51.42/7.03  --sat_finite_models                     false
% 51.42/7.03  --sat_fm_lemmas                         false
% 51.42/7.03  --sat_fm_prep                           false
% 51.42/7.03  --sat_fm_uc_incr                        true
% 51.42/7.03  --sat_out_model                         small
% 51.42/7.03  --sat_out_clauses                       false
% 51.42/7.03  
% 51.42/7.03  ------ QBF Options
% 51.42/7.03  
% 51.42/7.03  --qbf_mode                              false
% 51.42/7.03  --qbf_elim_univ                         false
% 51.42/7.03  --qbf_dom_inst                          none
% 51.42/7.03  --qbf_dom_pre_inst                      false
% 51.42/7.03  --qbf_sk_in                             false
% 51.42/7.03  --qbf_pred_elim                         true
% 51.42/7.03  --qbf_split                             512
% 51.42/7.03  
% 51.42/7.03  ------ BMC1 Options
% 51.42/7.03  
% 51.42/7.03  --bmc1_incremental                      false
% 51.42/7.03  --bmc1_axioms                           reachable_all
% 51.42/7.03  --bmc1_min_bound                        0
% 51.42/7.03  --bmc1_max_bound                        -1
% 51.42/7.03  --bmc1_max_bound_default                -1
% 51.42/7.03  --bmc1_symbol_reachability              true
% 51.42/7.03  --bmc1_property_lemmas                  false
% 51.42/7.03  --bmc1_k_induction                      false
% 51.42/7.03  --bmc1_non_equiv_states                 false
% 51.42/7.03  --bmc1_deadlock                         false
% 51.42/7.03  --bmc1_ucm                              false
% 51.42/7.03  --bmc1_add_unsat_core                   none
% 51.42/7.03  --bmc1_unsat_core_children              false
% 51.42/7.03  --bmc1_unsat_core_extrapolate_axioms    false
% 51.42/7.03  --bmc1_out_stat                         full
% 51.42/7.03  --bmc1_ground_init                      false
% 51.42/7.03  --bmc1_pre_inst_next_state              false
% 51.42/7.03  --bmc1_pre_inst_state                   false
% 51.42/7.03  --bmc1_pre_inst_reach_state             false
% 51.42/7.03  --bmc1_out_unsat_core                   false
% 51.42/7.03  --bmc1_aig_witness_out                  false
% 51.42/7.03  --bmc1_verbose                          false
% 51.42/7.03  --bmc1_dump_clauses_tptp                false
% 51.42/7.03  --bmc1_dump_unsat_core_tptp             false
% 51.42/7.03  --bmc1_dump_file                        -
% 51.42/7.03  --bmc1_ucm_expand_uc_limit              128
% 51.42/7.03  --bmc1_ucm_n_expand_iterations          6
% 51.42/7.03  --bmc1_ucm_extend_mode                  1
% 51.42/7.03  --bmc1_ucm_init_mode                    2
% 51.42/7.03  --bmc1_ucm_cone_mode                    none
% 51.42/7.03  --bmc1_ucm_reduced_relation_type        0
% 51.42/7.03  --bmc1_ucm_relax_model                  4
% 51.42/7.03  --bmc1_ucm_full_tr_after_sat            true
% 51.42/7.03  --bmc1_ucm_expand_neg_assumptions       false
% 51.42/7.03  --bmc1_ucm_layered_model                none
% 51.42/7.03  --bmc1_ucm_max_lemma_size               10
% 51.42/7.03  
% 51.42/7.03  ------ AIG Options
% 51.42/7.03  
% 51.42/7.03  --aig_mode                              false
% 51.42/7.03  
% 51.42/7.03  ------ Instantiation Options
% 51.42/7.03  
% 51.42/7.03  --instantiation_flag                    true
% 51.42/7.03  --inst_sos_flag                         true
% 51.42/7.03  --inst_sos_phase                        true
% 51.42/7.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.42/7.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.42/7.03  --inst_lit_sel_side                     none
% 51.42/7.03  --inst_solver_per_active                1400
% 51.42/7.03  --inst_solver_calls_frac                1.
% 51.42/7.03  --inst_passive_queue_type               priority_queues
% 51.42/7.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.42/7.03  --inst_passive_queues_freq              [25;2]
% 51.42/7.03  --inst_dismatching                      true
% 51.42/7.03  --inst_eager_unprocessed_to_passive     true
% 51.42/7.03  --inst_prop_sim_given                   true
% 51.42/7.03  --inst_prop_sim_new                     false
% 51.42/7.03  --inst_subs_new                         false
% 51.42/7.03  --inst_eq_res_simp                      false
% 51.42/7.03  --inst_subs_given                       false
% 51.42/7.03  --inst_orphan_elimination               true
% 51.42/7.03  --inst_learning_loop_flag               true
% 51.42/7.03  --inst_learning_start                   3000
% 51.42/7.03  --inst_learning_factor                  2
% 51.42/7.03  --inst_start_prop_sim_after_learn       3
% 51.42/7.03  --inst_sel_renew                        solver
% 51.42/7.03  --inst_lit_activity_flag                true
% 51.42/7.03  --inst_restr_to_given                   false
% 51.42/7.03  --inst_activity_threshold               500
% 51.42/7.03  --inst_out_proof                        true
% 51.42/7.03  
% 51.42/7.03  ------ Resolution Options
% 51.42/7.03  
% 51.42/7.03  --resolution_flag                       false
% 51.42/7.03  --res_lit_sel                           adaptive
% 51.42/7.03  --res_lit_sel_side                      none
% 51.42/7.03  --res_ordering                          kbo
% 51.42/7.03  --res_to_prop_solver                    active
% 51.42/7.03  --res_prop_simpl_new                    false
% 51.42/7.03  --res_prop_simpl_given                  true
% 51.42/7.03  --res_passive_queue_type                priority_queues
% 51.42/7.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.42/7.03  --res_passive_queues_freq               [15;5]
% 51.42/7.03  --res_forward_subs                      full
% 51.42/7.03  --res_backward_subs                     full
% 51.42/7.03  --res_forward_subs_resolution           true
% 51.42/7.03  --res_backward_subs_resolution          true
% 51.42/7.03  --res_orphan_elimination                true
% 51.42/7.03  --res_time_limit                        2.
% 51.42/7.03  --res_out_proof                         true
% 51.42/7.03  
% 51.42/7.03  ------ Superposition Options
% 51.42/7.03  
% 51.42/7.03  --superposition_flag                    true
% 51.42/7.03  --sup_passive_queue_type                priority_queues
% 51.42/7.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.42/7.03  --sup_passive_queues_freq               [8;1;4]
% 51.42/7.03  --demod_completeness_check              fast
% 51.42/7.03  --demod_use_ground                      true
% 51.42/7.03  --sup_to_prop_solver                    passive
% 51.42/7.03  --sup_prop_simpl_new                    true
% 51.42/7.03  --sup_prop_simpl_given                  true
% 51.42/7.03  --sup_fun_splitting                     true
% 51.42/7.03  --sup_smt_interval                      50000
% 51.42/7.03  
% 51.42/7.03  ------ Superposition Simplification Setup
% 51.42/7.03  
% 51.42/7.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.42/7.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.42/7.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.42/7.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.42/7.03  --sup_full_triv                         [TrivRules;PropSubs]
% 51.42/7.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.42/7.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.42/7.03  --sup_immed_triv                        [TrivRules]
% 51.42/7.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_immed_bw_main                     []
% 51.42/7.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.42/7.03  --sup_input_triv                        [Unflattening;TrivRules]
% 51.42/7.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.42/7.03  --sup_input_bw                          []
% 51.42/7.03  
% 51.42/7.03  ------ Combination Options
% 51.42/7.03  
% 51.42/7.03  --comb_res_mult                         3
% 51.42/7.03  --comb_sup_mult                         2
% 51.42/7.03  --comb_inst_mult                        10
% 51.42/7.03  
% 51.42/7.03  ------ Debug Options
% 51.42/7.03  
% 51.42/7.03  --dbg_backtrace                         false
% 51.42/7.03  --dbg_dump_prop_clauses                 false
% 51.42/7.03  --dbg_dump_prop_clauses_file            -
% 51.42/7.03  --dbg_out_stat                          false
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  ------ Proving...
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  % SZS status Theorem for theBenchmark.p
% 51.42/7.03  
% 51.42/7.03  % SZS output start CNFRefutation for theBenchmark.p
% 51.42/7.03  
% 51.42/7.03  fof(f18,conjecture,(
% 51.42/7.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f19,negated_conjecture,(
% 51.42/7.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 51.42/7.03    inference(negated_conjecture,[],[f18])).
% 51.42/7.03  
% 51.42/7.03  fof(f45,plain,(
% 51.42/7.03    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 51.42/7.03    inference(ennf_transformation,[],[f19])).
% 51.42/7.03  
% 51.42/7.03  fof(f46,plain,(
% 51.42/7.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 51.42/7.03    inference(flattening,[],[f45])).
% 51.42/7.03  
% 51.42/7.03  fof(f50,plain,(
% 51.42/7.03    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 51.42/7.03    introduced(choice_axiom,[])).
% 51.42/7.03  
% 51.42/7.03  fof(f49,plain,(
% 51.42/7.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 51.42/7.03    introduced(choice_axiom,[])).
% 51.42/7.03  
% 51.42/7.03  fof(f51,plain,(
% 51.42/7.03    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 51.42/7.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f50,f49])).
% 51.42/7.03  
% 51.42/7.03  fof(f80,plain,(
% 51.42/7.03    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f84,plain,(
% 51.42/7.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f13,axiom,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f37,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.42/7.03    inference(ennf_transformation,[],[f13])).
% 51.42/7.03  
% 51.42/7.03  fof(f38,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.42/7.03    inference(flattening,[],[f37])).
% 51.42/7.03  
% 51.42/7.03  fof(f71,plain,(
% 51.42/7.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f38])).
% 51.42/7.03  
% 51.42/7.03  fof(f81,plain,(
% 51.42/7.03    v1_funct_1(sK2)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f77,plain,(
% 51.42/7.03    v1_funct_1(sK1)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f7,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f28,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(ennf_transformation,[],[f7])).
% 51.42/7.03  
% 51.42/7.03  fof(f60,plain,(
% 51.42/7.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f28])).
% 51.42/7.03  
% 51.42/7.03  fof(f17,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f43,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.42/7.03    inference(ennf_transformation,[],[f17])).
% 51.42/7.03  
% 51.42/7.03  fof(f44,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.42/7.03    inference(flattening,[],[f43])).
% 51.42/7.03  
% 51.42/7.03  fof(f76,plain,(
% 51.42/7.03    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f44])).
% 51.42/7.03  
% 51.42/7.03  fof(f16,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f41,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.42/7.03    inference(ennf_transformation,[],[f16])).
% 51.42/7.03  
% 51.42/7.03  fof(f42,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.42/7.03    inference(flattening,[],[f41])).
% 51.42/7.03  
% 51.42/7.03  fof(f74,plain,(
% 51.42/7.03    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f42])).
% 51.42/7.03  
% 51.42/7.03  fof(f78,plain,(
% 51.42/7.03    v1_funct_2(sK1,sK0,sK0)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f9,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f31,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(ennf_transformation,[],[f9])).
% 51.42/7.03  
% 51.42/7.03  fof(f32,plain,(
% 51.42/7.03    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(flattening,[],[f31])).
% 51.42/7.03  
% 51.42/7.03  fof(f65,plain,(
% 51.42/7.03    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f32])).
% 51.42/7.03  
% 51.42/7.03  fof(f79,plain,(
% 51.42/7.03    v3_funct_2(sK1,sK0,sK0)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f6,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f21,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 51.42/7.03    inference(pure_predicate_removal,[],[f6])).
% 51.42/7.03  
% 51.42/7.03  fof(f27,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(ennf_transformation,[],[f21])).
% 51.42/7.03  
% 51.42/7.03  fof(f59,plain,(
% 51.42/7.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f27])).
% 51.42/7.03  
% 51.42/7.03  fof(f10,axiom,(
% 51.42/7.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f33,plain,(
% 51.42/7.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 51.42/7.03    inference(ennf_transformation,[],[f10])).
% 51.42/7.03  
% 51.42/7.03  fof(f34,plain,(
% 51.42/7.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 51.42/7.03    inference(flattening,[],[f33])).
% 51.42/7.03  
% 51.42/7.03  fof(f48,plain,(
% 51.42/7.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 51.42/7.03    inference(nnf_transformation,[],[f34])).
% 51.42/7.03  
% 51.42/7.03  fof(f66,plain,(
% 51.42/7.03    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f48])).
% 51.42/7.03  
% 51.42/7.03  fof(f5,axiom,(
% 51.42/7.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f26,plain,(
% 51.42/7.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(ennf_transformation,[],[f5])).
% 51.42/7.03  
% 51.42/7.03  fof(f58,plain,(
% 51.42/7.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f26])).
% 51.42/7.03  
% 51.42/7.03  fof(f82,plain,(
% 51.42/7.03    v1_funct_2(sK2,sK0,sK0)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f85,plain,(
% 51.42/7.03    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f86,plain,(
% 51.42/7.03    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f14,axiom,(
% 51.42/7.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f39,plain,(
% 51.42/7.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 51.42/7.03    inference(ennf_transformation,[],[f14])).
% 51.42/7.03  
% 51.42/7.03  fof(f40,plain,(
% 51.42/7.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 51.42/7.03    inference(flattening,[],[f39])).
% 51.42/7.03  
% 51.42/7.03  fof(f72,plain,(
% 51.42/7.03    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f40])).
% 51.42/7.03  
% 51.42/7.03  fof(f8,axiom,(
% 51.42/7.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f29,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 51.42/7.03    inference(ennf_transformation,[],[f8])).
% 51.42/7.03  
% 51.42/7.03  fof(f30,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(flattening,[],[f29])).
% 51.42/7.03  
% 51.42/7.03  fof(f47,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.42/7.03    inference(nnf_transformation,[],[f30])).
% 51.42/7.03  
% 51.42/7.03  fof(f62,plain,(
% 51.42/7.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f47])).
% 51.42/7.03  
% 51.42/7.03  fof(f89,plain,(
% 51.42/7.03    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(equality_resolution,[],[f62])).
% 51.42/7.03  
% 51.42/7.03  fof(f2,axiom,(
% 51.42/7.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f22,plain,(
% 51.42/7.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 51.42/7.03    inference(ennf_transformation,[],[f2])).
% 51.42/7.03  
% 51.42/7.03  fof(f23,plain,(
% 51.42/7.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 51.42/7.03    inference(flattening,[],[f22])).
% 51.42/7.03  
% 51.42/7.03  fof(f55,plain,(
% 51.42/7.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f23])).
% 51.42/7.03  
% 51.42/7.03  fof(f83,plain,(
% 51.42/7.03    v3_funct_2(sK2,sK0,sK0)),
% 51.42/7.03    inference(cnf_transformation,[],[f51])).
% 51.42/7.03  
% 51.42/7.03  fof(f3,axiom,(
% 51.42/7.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f56,plain,(
% 51.42/7.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 51.42/7.03    inference(cnf_transformation,[],[f3])).
% 51.42/7.03  
% 51.42/7.03  fof(f15,axiom,(
% 51.42/7.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f73,plain,(
% 51.42/7.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f15])).
% 51.42/7.03  
% 51.42/7.03  fof(f87,plain,(
% 51.42/7.03    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 51.42/7.03    inference(definition_unfolding,[],[f56,f73])).
% 51.42/7.03  
% 51.42/7.03  fof(f11,axiom,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f35,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.42/7.03    inference(ennf_transformation,[],[f11])).
% 51.42/7.03  
% 51.42/7.03  fof(f36,plain,(
% 51.42/7.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.42/7.03    inference(flattening,[],[f35])).
% 51.42/7.03  
% 51.42/7.03  fof(f69,plain,(
% 51.42/7.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f36])).
% 51.42/7.03  
% 51.42/7.03  fof(f61,plain,(
% 51.42/7.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f47])).
% 51.42/7.03  
% 51.42/7.03  fof(f12,axiom,(
% 51.42/7.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f20,plain,(
% 51.42/7.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 51.42/7.03    inference(pure_predicate_removal,[],[f12])).
% 51.42/7.03  
% 51.42/7.03  fof(f70,plain,(
% 51.42/7.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f20])).
% 51.42/7.03  
% 51.42/7.03  fof(f4,axiom,(
% 51.42/7.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f24,plain,(
% 51.42/7.03    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.42/7.03    inference(ennf_transformation,[],[f4])).
% 51.42/7.03  
% 51.42/7.03  fof(f25,plain,(
% 51.42/7.03    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.42/7.03    inference(flattening,[],[f24])).
% 51.42/7.03  
% 51.42/7.03  fof(f57,plain,(
% 51.42/7.03    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.42/7.03    inference(cnf_transformation,[],[f25])).
% 51.42/7.03  
% 51.42/7.03  fof(f88,plain,(
% 51.42/7.03    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.42/7.03    inference(definition_unfolding,[],[f57,f73])).
% 51.42/7.03  
% 51.42/7.03  fof(f1,axiom,(
% 51.42/7.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 51.42/7.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.42/7.03  
% 51.42/7.03  fof(f52,plain,(
% 51.42/7.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 51.42/7.03    inference(cnf_transformation,[],[f1])).
% 51.42/7.03  
% 51.42/7.03  fof(f53,plain,(
% 51.42/7.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 51.42/7.03    inference(cnf_transformation,[],[f1])).
% 51.42/7.03  
% 51.42/7.03  fof(f64,plain,(
% 51.42/7.03    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.42/7.03    inference(cnf_transformation,[],[f32])).
% 51.42/7.03  
% 51.42/7.03  cnf(c_30,negated_conjecture,
% 51.42/7.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.42/7.03      inference(cnf_transformation,[],[f80]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1659,negated_conjecture,
% 51.42/7.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_30]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2206,plain,
% 51.42/7.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_26,negated_conjecture,
% 51.42/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.42/7.03      inference(cnf_transformation,[],[f84]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1662,negated_conjecture,
% 51.42/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_26]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2203,plain,
% 51.42/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1662]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_19,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | ~ v1_funct_1(X3)
% 51.42/7.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f71]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1667,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 51.42/7.03      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
% 51.42/7.03      | ~ v1_funct_1(X3_51)
% 51.42/7.03      | ~ v1_funct_1(X0_51)
% 51.42/7.03      | k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51) = k5_relat_1(X3_51,X0_51) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_19]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2198,plain,
% 51.42/7.03      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X4_51,X5_51) = k5_relat_1(X4_51,X5_51)
% 51.42/7.03      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 51.42/7.03      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 51.42/7.03      | v1_funct_1(X4_51) != iProver_top
% 51.42/7.03      | v1_funct_1(X5_51) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1667]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3860,plain,
% 51.42/7.03      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 51.42/7.03      | v1_funct_1(X2_51) != iProver_top
% 51.42/7.03      | v1_funct_1(sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2203,c_2198]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_29,negated_conjecture,
% 51.42/7.03      ( v1_funct_1(sK2) ),
% 51.42/7.03      inference(cnf_transformation,[],[f81]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_38,plain,
% 51.42/7.03      ( v1_funct_1(sK2) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4300,plain,
% 51.42/7.03      ( v1_funct_1(X2_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 51.42/7.03      | k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2) ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_3860,c_38]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4301,plain,
% 51.42/7.03      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X2_51,sK2) = k5_relat_1(X2_51,sK2)
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 51.42/7.03      | v1_funct_1(X2_51) != iProver_top ),
% 51.42/7.03      inference(renaming,[status(thm)],[c_4300]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4307,plain,
% 51.42/7.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 51.42/7.03      | v1_funct_1(sK1) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2206,c_4301]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_33,negated_conjecture,
% 51.42/7.03      ( v1_funct_1(sK1) ),
% 51.42/7.03      inference(cnf_transformation,[],[f77]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4088,plain,
% 51.42/7.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK1)
% 51.42/7.03      | ~ v1_funct_1(sK2)
% 51.42/7.03      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 51.42/7.03      inference(instantiation,[status(thm)],[c_1667]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4595,plain,
% 51.42/7.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_4307,c_33,c_30,c_29,c_26,c_4088]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_8,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f60]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1673,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 51.42/7.03      | k2_relset_1(X1_51,X2_51,X0_51) = k2_relat_1(X0_51) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_8]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2192,plain,
% 51.42/7.03      ( k2_relset_1(X0_51,X1_51,X2_51) = k2_relat_1(X2_51)
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1673]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3361,plain,
% 51.42/7.03      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2206,c_2192]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_23,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 51.42/7.03      | ~ v1_funct_2(X3,X1,X0)
% 51.42/7.03      | ~ v1_funct_2(X2,X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 51.42/7.03      | ~ v1_funct_1(X2)
% 51.42/7.03      | ~ v1_funct_1(X3)
% 51.42/7.03      | ~ v2_funct_1(X2)
% 51.42/7.03      | k2_relset_1(X0,X1,X2) != X1
% 51.42/7.03      | k2_funct_1(X2) = X3
% 51.42/7.03      | k1_xboole_0 = X0
% 51.42/7.03      | k1_xboole_0 = X1 ),
% 51.42/7.03      inference(cnf_transformation,[],[f76]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_22,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 51.42/7.03      | ~ v1_funct_2(X3,X1,X0)
% 51.42/7.03      | ~ v1_funct_2(X2,X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 51.42/7.03      | ~ v1_funct_1(X2)
% 51.42/7.03      | ~ v1_funct_1(X3)
% 51.42/7.03      | v2_funct_1(X2) ),
% 51.42/7.03      inference(cnf_transformation,[],[f74]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_178,plain,
% 51.42/7.03      ( ~ v1_funct_1(X3)
% 51.42/7.03      | ~ v1_funct_1(X2)
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | ~ v1_funct_2(X2,X0,X1)
% 51.42/7.03      | ~ v1_funct_2(X3,X1,X0)
% 51.42/7.03      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 51.42/7.03      | k2_relset_1(X0,X1,X2) != X1
% 51.42/7.03      | k2_funct_1(X2) = X3
% 51.42/7.03      | k1_xboole_0 = X0
% 51.42/7.03      | k1_xboole_0 = X1 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_23,c_22]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_179,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 51.42/7.03      | ~ v1_funct_2(X3,X1,X0)
% 51.42/7.03      | ~ v1_funct_2(X2,X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 51.42/7.03      | ~ v1_funct_1(X2)
% 51.42/7.03      | ~ v1_funct_1(X3)
% 51.42/7.03      | k2_relset_1(X0,X1,X2) != X1
% 51.42/7.03      | k2_funct_1(X2) = X3
% 51.42/7.03      | k1_xboole_0 = X0
% 51.42/7.03      | k1_xboole_0 = X1 ),
% 51.42/7.03      inference(renaming,[status(thm)],[c_178]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1656,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51))
% 51.42/7.03      | ~ v1_funct_2(X3_51,X1_51,X0_51)
% 51.42/7.03      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 51.42/7.03      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 51.42/7.03      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 51.42/7.03      | ~ v1_funct_1(X2_51)
% 51.42/7.03      | ~ v1_funct_1(X3_51)
% 51.42/7.03      | k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 51.42/7.03      | k2_funct_1(X2_51) = X3_51
% 51.42/7.03      | k1_xboole_0 = X0_51
% 51.42/7.03      | k1_xboole_0 = X1_51 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_179]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2209,plain,
% 51.42/7.03      ( k2_relset_1(X0_51,X1_51,X2_51) != X1_51
% 51.42/7.03      | k2_funct_1(X2_51) = X3_51
% 51.42/7.03      | k1_xboole_0 = X0_51
% 51.42/7.03      | k1_xboole_0 = X1_51
% 51.42/7.03      | r2_relset_1(X0_51,X0_51,k1_partfun1(X0_51,X1_51,X1_51,X0_51,X2_51,X3_51),k6_partfun1(X0_51)) != iProver_top
% 51.42/7.03      | v1_funct_2(X3_51,X1_51,X0_51) != iProver_top
% 51.42/7.03      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 51.42/7.03      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 51.42/7.03      | v1_funct_1(X2_51) != iProver_top
% 51.42/7.03      | v1_funct_1(X3_51) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5096,plain,
% 51.42/7.03      ( k2_funct_1(sK1) = X0_51
% 51.42/7.03      | k2_relat_1(sK1) != sK0
% 51.42/7.03      | sK0 = k1_xboole_0
% 51.42/7.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 51.42/7.03      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 51.42/7.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(X0_51) != iProver_top
% 51.42/7.03      | v1_funct_1(sK1) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_3361,c_2209]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_34,plain,
% 51.42/7.03      ( v1_funct_1(sK1) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_32,negated_conjecture,
% 51.42/7.03      ( v1_funct_2(sK1,sK0,sK0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f78]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_35,plain,
% 51.42/7.03      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_37,plain,
% 51.42/7.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_11,plain,
% 51.42/7.03      ( ~ v3_funct_2(X0,X1,X2)
% 51.42/7.03      | v2_funct_2(X0,X2)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | ~ v1_funct_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f65]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_31,negated_conjecture,
% 51.42/7.03      ( v3_funct_2(sK1,sK0,sK0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f79]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_490,plain,
% 51.42/7.03      ( v2_funct_2(X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | sK1 != X0
% 51.42/7.03      | sK0 != X1
% 51.42/7.03      | sK0 != X2 ),
% 51.42/7.03      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_491,plain,
% 51.42/7.03      ( v2_funct_2(sK1,sK0)
% 51.42/7.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK1) ),
% 51.42/7.03      inference(unflattening,[status(thm)],[c_490]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_492,plain,
% 51.42/7.03      ( v2_funct_2(sK1,sK0) = iProver_top
% 51.42/7.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(sK1) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_7,plain,
% 51.42/7.03      ( v5_relat_1(X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 51.42/7.03      inference(cnf_transformation,[],[f59]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_15,plain,
% 51.42/7.03      ( ~ v2_funct_2(X0,X1)
% 51.42/7.03      | ~ v5_relat_1(X0,X1)
% 51.42/7.03      | ~ v1_relat_1(X0)
% 51.42/7.03      | k2_relat_1(X0) = X1 ),
% 51.42/7.03      inference(cnf_transformation,[],[f66]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_344,plain,
% 51.42/7.03      ( ~ v2_funct_2(X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.42/7.03      | ~ v1_relat_1(X0)
% 51.42/7.03      | k2_relat_1(X0) = X1 ),
% 51.42/7.03      inference(resolution,[status(thm)],[c_7,c_15]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_6,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | v1_relat_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f58]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_356,plain,
% 51.42/7.03      ( ~ v2_funct_2(X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.42/7.03      | k2_relat_1(X0) = X1 ),
% 51.42/7.03      inference(forward_subsumption_resolution,[status(thm)],[c_344,c_6]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1655,plain,
% 51.42/7.03      ( ~ v2_funct_2(X0_51,X1_51)
% 51.42/7.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 51.42/7.03      | k2_relat_1(X0_51) = X1_51 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_356]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2210,plain,
% 51.42/7.03      ( k2_relat_1(X0_51) = X1_51
% 51.42/7.03      | v2_funct_2(X0_51,X1_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51))) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5623,plain,
% 51.42/7.03      ( k2_relat_1(sK1) = sK0 | v2_funct_2(sK1,sK0) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2206,c_2210]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9682,plain,
% 51.42/7.03      ( v1_funct_1(X0_51) != iProver_top
% 51.42/7.03      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 51.42/7.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 51.42/7.03      | sK0 = k1_xboole_0
% 51.42/7.03      | k2_funct_1(sK1) = X0_51
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_5096,c_34,c_35,c_37,c_492,c_5623]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9683,plain,
% 51.42/7.03      ( k2_funct_1(sK1) = X0_51
% 51.42/7.03      | sK0 = k1_xboole_0
% 51.42/7.03      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X0_51),k6_partfun1(sK0)) != iProver_top
% 51.42/7.03      | v1_funct_2(X0_51,sK0,sK0) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(X0_51) != iProver_top ),
% 51.42/7.03      inference(renaming,[status(thm)],[c_9682]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9688,plain,
% 51.42/7.03      ( k2_funct_1(sK1) = sK2
% 51.42/7.03      | sK0 = k1_xboole_0
% 51.42/7.03      | r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) != iProver_top
% 51.42/7.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.42/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_4595,c_9683]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_28,negated_conjecture,
% 51.42/7.03      ( v1_funct_2(sK2,sK0,sK0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f82]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_25,negated_conjecture,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 51.42/7.03      inference(cnf_transformation,[],[f85]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1663,negated_conjecture,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_25]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2202,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4597,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_4595,c_2202]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4598,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0)) ),
% 51.42/7.03      inference(predicate_to_equality_rev,[status(thm)],[c_4597]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9690,plain,
% 51.42/7.03      ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_partfun1(sK0))
% 51.42/7.03      | ~ v1_funct_2(sK2,sK0,sK0)
% 51.42/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK2)
% 51.42/7.03      | k2_funct_1(sK1) = sK2
% 51.42/7.03      | sK0 = k1_xboole_0 ),
% 51.42/7.03      inference(predicate_to_equality_rev,[status(thm)],[c_9688]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9693,plain,
% 51.42/7.03      ( k2_funct_1(sK1) = sK2 | sK0 = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_9688,c_29,c_28,c_26,c_4598,c_9690]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_24,negated_conjecture,
% 51.42/7.03      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 51.42/7.03      inference(cnf_transformation,[],[f86]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1664,negated_conjecture,
% 51.42/7.03      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_24]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2201,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_20,plain,
% 51.42/7.03      ( ~ v1_funct_2(X0,X1,X1)
% 51.42/7.03      | ~ v3_funct_2(X0,X1,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f72]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_509,plain,
% 51.42/7.03      ( ~ v1_funct_2(X0,X1,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 51.42/7.03      | sK1 != X0
% 51.42/7.03      | sK0 != X1 ),
% 51.42/7.03      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_510,plain,
% 51.42/7.03      ( ~ v1_funct_2(sK1,sK0,sK0)
% 51.42/7.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK1)
% 51.42/7.03      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 51.42/7.03      inference(unflattening,[status(thm)],[c_509]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_512,plain,
% 51.42/7.03      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_510,c_33,c_32,c_30]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1648,plain,
% 51.42/7.03      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_512]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2216,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 51.42/7.03      inference(light_normalisation,[status(thm)],[c_2201,c_1648]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9695,plain,
% 51.42/7.03      ( sK0 = k1_xboole_0 | r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_9693,c_2216]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_41,plain,
% 51.42/7.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9,plain,
% 51.42/7.03      ( r2_relset_1(X0,X1,X2,X2)
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 51.42/7.03      inference(cnf_transformation,[],[f89]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1672,plain,
% 51.42/7.03      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51)
% 51.42/7.03      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_9]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2278,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,sK2,sK2)
% 51.42/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.42/7.03      inference(instantiation,[status(thm)],[c_1672]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2279,plain,
% 51.42/7.03      ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
% 51.42/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_2278]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9769,plain,
% 51.42/7.03      ( sK0 = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_9695,c_41,c_2279]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5798,plain,
% 51.42/7.03      ( k2_relat_1(sK1) = sK0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_5623,c_34,c_37,c_492]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2,plain,
% 51.42/7.03      ( ~ v1_relat_1(X0)
% 51.42/7.03      | k2_relat_1(X0) != k1_xboole_0
% 51.42/7.03      | k1_xboole_0 = X0 ),
% 51.42/7.03      inference(cnf_transformation,[],[f55]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1678,plain,
% 51.42/7.03      ( ~ v1_relat_1(X0_51)
% 51.42/7.03      | k2_relat_1(X0_51) != k1_xboole_0
% 51.42/7.03      | k1_xboole_0 = X0_51 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_2]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2188,plain,
% 51.42/7.03      ( k2_relat_1(X0_51) != k1_xboole_0
% 51.42/7.03      | k1_xboole_0 = X0_51
% 51.42/7.03      | v1_relat_1(X0_51) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1678]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5802,plain,
% 51.42/7.03      ( sK1 = k1_xboole_0
% 51.42/7.03      | sK0 != k1_xboole_0
% 51.42/7.03      | v1_relat_1(sK1) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_5798,c_2188]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1674,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 51.42/7.03      | v1_relat_1(X0_51) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_6]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2191,plain,
% 51.42/7.03      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 51.42/7.03      | v1_relat_1(X0_51) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1674]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3153,plain,
% 51.42/7.03      ( v1_relat_1(sK1) = iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2206,c_2191]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5987,plain,
% 51.42/7.03      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_5802,c_3153]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5988,plain,
% 51.42/7.03      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 51.42/7.03      inference(renaming,[status(thm)],[c_5987]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9807,plain,
% 51.42/7.03      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9769,c_5988]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9875,plain,
% 51.42/7.03      ( sK1 = k1_xboole_0 ),
% 51.42/7.03      inference(equality_resolution_simp,[status(thm)],[c_9807]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5622,plain,
% 51.42/7.03      ( k2_relat_1(sK2) = sK0 | v2_funct_2(sK2,sK0) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2203,c_2210]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_27,negated_conjecture,
% 51.42/7.03      ( v3_funct_2(sK2,sK0,sK0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f83]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_468,plain,
% 51.42/7.03      ( v2_funct_2(X0,X1)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | sK2 != X0
% 51.42/7.03      | sK0 != X1
% 51.42/7.03      | sK0 != X2 ),
% 51.42/7.03      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_469,plain,
% 51.42/7.03      ( v2_funct_2(sK2,sK0)
% 51.42/7.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK2) ),
% 51.42/7.03      inference(unflattening,[status(thm)],[c_468]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_470,plain,
% 51.42/7.03      ( v2_funct_2(sK2,sK0) = iProver_top
% 51.42/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(sK2) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5790,plain,
% 51.42/7.03      ( k2_relat_1(sK2) = sK0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_5622,c_38,c_41,c_470]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5794,plain,
% 51.42/7.03      ( sK2 = k1_xboole_0
% 51.42/7.03      | sK0 != k1_xboole_0
% 51.42/7.03      | v1_relat_1(sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_5790,c_2188]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3144,plain,
% 51.42/7.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 51.42/7.03      | v1_relat_1(sK2) ),
% 51.42/7.03      inference(instantiation,[status(thm)],[c_1674]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3146,plain,
% 51.42/7.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | v1_relat_1(sK2) ),
% 51.42/7.03      inference(instantiation,[status(thm)],[c_3144]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5796,plain,
% 51.42/7.03      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 51.42/7.03      inference(predicate_to_equality_rev,[status(thm)],[c_5794]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5984,plain,
% 51.42/7.03      ( sK0 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_5794,c_26,c_3146,c_5796]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5985,plain,
% 51.42/7.03      ( sK2 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 51.42/7.03      inference(renaming,[status(thm)],[c_5984]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9808,plain,
% 51.42/7.03      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9769,c_5985]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9850,plain,
% 51.42/7.03      ( sK2 = k1_xboole_0 ),
% 51.42/7.03      inference(equality_resolution_simp,[status(thm)],[c_9808]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9828,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k6_partfun1(k1_xboole_0)) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9769,c_4597]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4,plain,
% 51.42/7.03      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(cnf_transformation,[],[f87]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1676,plain,
% 51.42/7.03      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_4]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9847,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,sK2),k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(light_normalisation,[status(thm)],[c_9828,c_1676]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9862,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK1,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9850,c_9847]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9879,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9875,c_9862]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4306,plain,
% 51.42/7.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
% 51.42/7.03      | v1_funct_1(sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2203,c_4301]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4321,plain,
% 51.42/7.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_4306,c_38]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_16,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.42/7.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | ~ v1_funct_1(X3) ),
% 51.42/7.03      inference(cnf_transformation,[],[f69]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1670,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 51.42/7.03      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51)))
% 51.42/7.03      | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 51.42/7.03      | ~ v1_funct_1(X3_51)
% 51.42/7.03      | ~ v1_funct_1(X0_51) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_16]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2195,plain,
% 51.42/7.03      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 51.42/7.03      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X5_51))) != iProver_top
% 51.42/7.03      | m1_subset_1(k1_partfun1(X4_51,X5_51,X1_51,X2_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) = iProver_top
% 51.42/7.03      | v1_funct_1(X3_51) != iProver_top
% 51.42/7.03      | v1_funct_1(X0_51) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_4324,plain,
% 51.42/7.03      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 51.42/7.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.42/7.03      | v1_funct_1(sK2) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_4321,c_2195]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5419,plain,
% 51.42/7.03      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_4324,c_38,c_41]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_10,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0,X1,X2,X3)
% 51.42/7.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.42/7.03      | X3 = X2 ),
% 51.42/7.03      inference(cnf_transformation,[],[f61]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1671,plain,
% 51.42/7.03      ( ~ r2_relset_1(X0_51,X1_51,X2_51,X3_51)
% 51.42/7.03      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 51.42/7.03      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 51.42/7.03      | X3_51 = X2_51 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_10]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2194,plain,
% 51.42/7.03      ( X0_51 = X1_51
% 51.42/7.03      | r2_relset_1(X2_51,X3_51,X1_51,X0_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1671]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5429,plain,
% 51.42/7.03      ( k5_relat_1(sK2,sK2) = X0_51
% 51.42/7.03      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK2),X0_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_5419,c_2194]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9793,plain,
% 51.42/7.03      ( k5_relat_1(sK2,sK2) = X0_51
% 51.42/7.03      | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(sK2,sK2),X0_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9769,c_5429]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9908,plain,
% 51.42/7.03      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = X0_51
% 51.42/7.03      | r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0),X0_51) != iProver_top
% 51.42/7.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9793,c_9850]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_23321,plain,
% 51.42/7.03      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 51.42/7.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_9879,c_9908]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_18,plain,
% 51.42/7.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 51.42/7.03      inference(cnf_transformation,[],[f70]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1668,plain,
% 51.42/7.03      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_18]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2197,plain,
% 51.42/7.03      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2797,plain,
% 51.42/7.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_1676,c_2197]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_134487,plain,
% 51.42/7.03      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_23321,c_2797]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_5,plain,
% 51.42/7.03      ( ~ v1_funct_1(X0)
% 51.42/7.03      | ~ v1_funct_1(X1)
% 51.42/7.03      | ~ v2_funct_1(X1)
% 51.42/7.03      | ~ v1_relat_1(X1)
% 51.42/7.03      | ~ v1_relat_1(X0)
% 51.42/7.03      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 51.42/7.03      | k2_funct_1(X1) = X0
% 51.42/7.03      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f88]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1675,plain,
% 51.42/7.03      ( ~ v1_funct_1(X0_51)
% 51.42/7.03      | ~ v1_funct_1(X1_51)
% 51.42/7.03      | ~ v2_funct_1(X1_51)
% 51.42/7.03      | ~ v1_relat_1(X1_51)
% 51.42/7.03      | ~ v1_relat_1(X0_51)
% 51.42/7.03      | k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
% 51.42/7.03      | k2_funct_1(X1_51) = X0_51
% 51.42/7.03      | k1_relat_1(X1_51) != k2_relat_1(X0_51) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_5]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2190,plain,
% 51.42/7.03      ( k5_relat_1(X0_51,X1_51) != k6_partfun1(k2_relat_1(X1_51))
% 51.42/7.03      | k2_funct_1(X1_51) = X0_51
% 51.42/7.03      | k1_relat_1(X1_51) != k2_relat_1(X0_51)
% 51.42/7.03      | v1_funct_1(X1_51) != iProver_top
% 51.42/7.03      | v1_funct_1(X0_51) != iProver_top
% 51.42/7.03      | v2_funct_1(X1_51) != iProver_top
% 51.42/7.03      | v1_relat_1(X0_51) != iProver_top
% 51.42/7.03      | v1_relat_1(X1_51) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1675]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_135524,plain,
% 51.42/7.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 51.42/7.03      | k6_partfun1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
% 51.42/7.03      | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
% 51.42/7.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v2_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_134487,c_2190]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1,plain,
% 51.42/7.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(cnf_transformation,[],[f52]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1679,plain,
% 51.42/7.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_1]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_0,plain,
% 51.42/7.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(cnf_transformation,[],[f53]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1680,plain,
% 51.42/7.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_0]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_135525,plain,
% 51.42/7.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 51.42/7.03      | k1_xboole_0 != k1_xboole_0
% 51.42/7.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v2_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 51.42/7.03      inference(light_normalisation,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_135524,c_1676,c_1679,c_1680]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_135526,plain,
% 51.42/7.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 51.42/7.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v2_funct_1(k1_xboole_0) != iProver_top
% 51.42/7.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 51.42/7.03      inference(equality_resolution_simp,[status(thm)],[c_135525]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3155,plain,
% 51.42/7.03      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2797,c_2191]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_12,plain,
% 51.42/7.03      ( ~ v3_funct_2(X0,X1,X2)
% 51.42/7.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | v2_funct_1(X0) ),
% 51.42/7.03      inference(cnf_transformation,[],[f64]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_457,plain,
% 51.42/7.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.42/7.03      | ~ v1_funct_1(X0)
% 51.42/7.03      | v2_funct_1(X0)
% 51.42/7.03      | sK2 != X0
% 51.42/7.03      | sK0 != X2
% 51.42/7.03      | sK0 != X1 ),
% 51.42/7.03      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_458,plain,
% 51.42/7.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.42/7.03      | ~ v1_funct_1(sK2)
% 51.42/7.03      | v2_funct_1(sK2) ),
% 51.42/7.03      inference(unflattening,[status(thm)],[c_457]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_460,plain,
% 51.42/7.03      ( v2_funct_1(sK2) ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_458,c_29,c_26]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1653,plain,
% 51.42/7.03      ( v2_funct_1(sK2) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_460]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2212,plain,
% 51.42/7.03      ( v2_funct_1(sK2) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_13682,plain,
% 51.42/7.03      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9850,c_2212]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_1660,negated_conjecture,
% 51.42/7.03      ( v1_funct_1(sK2) ),
% 51.42/7.03      inference(subtyping,[status(esa)],[c_29]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2205,plain,
% 51.42/7.03      ( v1_funct_1(sK2) = iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_13683,plain,
% 51.42/7.03      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9850,c_2205]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_135687,plain,
% 51.42/7.03      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 51.42/7.03      inference(global_propositional_subsumption,
% 51.42/7.03                [status(thm)],
% 51.42/7.03                [c_135526,c_3155,c_13682,c_13683]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9838,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9769,c_2216]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9870,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(sK1)) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9850,c_9838]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_9881,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_9875,c_9870]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_135689,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 51.42/7.03      inference(demodulation,[status(thm)],[c_135687,c_9881]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_2193,plain,
% 51.42/7.03      ( r2_relset_1(X0_51,X1_51,X2_51,X2_51) = iProver_top
% 51.42/7.03      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 51.42/7.03      inference(predicate_to_equality,[status(thm)],[c_1672]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(c_3796,plain,
% 51.42/7.03      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 51.42/7.03      inference(superposition,[status(thm)],[c_2797,c_2193]) ).
% 51.42/7.03  
% 51.42/7.03  cnf(contradiction,plain,
% 51.42/7.03      ( $false ),
% 51.42/7.03      inference(minisat,[status(thm)],[c_135689,c_3796]) ).
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  % SZS output end CNFRefutation for theBenchmark.p
% 51.42/7.03  
% 51.42/7.03  ------                               Statistics
% 51.42/7.03  
% 51.42/7.03  ------ General
% 51.42/7.03  
% 51.42/7.03  abstr_ref_over_cycles:                  0
% 51.42/7.03  abstr_ref_under_cycles:                 0
% 51.42/7.03  gc_basic_clause_elim:                   0
% 51.42/7.03  forced_gc_time:                         0
% 51.42/7.03  parsing_time:                           0.008
% 51.42/7.03  unif_index_cands_time:                  0.
% 51.42/7.03  unif_index_add_time:                    0.
% 51.42/7.03  orderings_time:                         0.
% 51.42/7.03  out_proof_time:                         0.038
% 51.42/7.03  total_time:                             6.225
% 51.42/7.03  num_of_symbols:                         57
% 51.42/7.03  num_of_terms:                           141741
% 51.42/7.03  
% 51.42/7.03  ------ Preprocessing
% 51.42/7.03  
% 51.42/7.03  num_of_splits:                          0
% 51.42/7.03  num_of_split_atoms:                     0
% 51.42/7.03  num_of_reused_defs:                     0
% 51.42/7.03  num_eq_ax_congr_red:                    22
% 51.42/7.03  num_of_sem_filtered_clauses:            1
% 51.42/7.03  num_of_subtypes:                        3
% 51.42/7.03  monotx_restored_types:                  1
% 51.42/7.03  sat_num_of_epr_types:                   0
% 51.42/7.03  sat_num_of_non_cyclic_types:            0
% 51.42/7.03  sat_guarded_non_collapsed_types:        1
% 51.42/7.03  num_pure_diseq_elim:                    0
% 51.42/7.03  simp_replaced_by:                       0
% 51.42/7.03  res_preprocessed:                       169
% 51.42/7.03  prep_upred:                             0
% 51.42/7.03  prep_unflattend:                        92
% 51.42/7.03  smt_new_axioms:                         0
% 51.42/7.03  pred_elim_cands:                        7
% 51.42/7.03  pred_elim:                              2
% 51.42/7.03  pred_elim_cl:                           0
% 51.42/7.03  pred_elim_cycles:                       9
% 51.42/7.03  merged_defs:                            0
% 51.42/7.03  merged_defs_ncl:                        0
% 51.42/7.03  bin_hyper_res:                          0
% 51.42/7.03  prep_cycles:                            4
% 51.42/7.03  pred_elim_time:                         0.018
% 51.42/7.03  splitting_time:                         0.
% 51.42/7.03  sem_filter_time:                        0.
% 51.42/7.03  monotx_time:                            0.
% 51.42/7.03  subtype_inf_time:                       0.001
% 51.42/7.03  
% 51.42/7.03  ------ Problem properties
% 51.42/7.03  
% 51.42/7.03  clauses:                                33
% 51.42/7.03  conjectures:                            8
% 51.42/7.03  epr:                                    8
% 51.42/7.03  horn:                                   32
% 51.42/7.03  ground:                                 17
% 51.42/7.03  unary:                                  18
% 51.42/7.03  binary:                                 4
% 51.42/7.03  lits:                                   89
% 51.42/7.03  lits_eq:                                20
% 51.42/7.03  fd_pure:                                0
% 51.42/7.03  fd_pseudo:                              0
% 51.42/7.03  fd_cond:                                2
% 51.42/7.03  fd_pseudo_cond:                         4
% 51.42/7.03  ac_symbols:                             0
% 51.42/7.03  
% 51.42/7.03  ------ Propositional Solver
% 51.42/7.03  
% 51.42/7.03  prop_solver_calls:                      51
% 51.42/7.03  prop_fast_solver_calls:                 6269
% 51.42/7.03  smt_solver_calls:                       0
% 51.42/7.03  smt_fast_solver_calls:                  0
% 51.42/7.03  prop_num_of_clauses:                    50729
% 51.42/7.03  prop_preprocess_simplified:             59946
% 51.42/7.03  prop_fo_subsumed:                       1554
% 51.42/7.03  prop_solver_time:                       0.
% 51.42/7.03  smt_solver_time:                        0.
% 51.42/7.03  smt_fast_solver_time:                   0.
% 51.42/7.03  prop_fast_solver_time:                  0.
% 51.42/7.03  prop_unsat_core_time:                   0.009
% 51.42/7.03  
% 51.42/7.03  ------ QBF
% 51.42/7.03  
% 51.42/7.03  qbf_q_res:                              0
% 51.42/7.03  qbf_num_tautologies:                    0
% 51.42/7.03  qbf_prep_cycles:                        0
% 51.42/7.03  
% 51.42/7.03  ------ BMC1
% 51.42/7.03  
% 51.42/7.03  bmc1_current_bound:                     -1
% 51.42/7.03  bmc1_last_solved_bound:                 -1
% 51.42/7.03  bmc1_unsat_core_size:                   -1
% 51.42/7.03  bmc1_unsat_core_parents_size:           -1
% 51.42/7.03  bmc1_merge_next_fun:                    0
% 51.42/7.03  bmc1_unsat_core_clauses_time:           0.
% 51.42/7.03  
% 51.42/7.03  ------ Instantiation
% 51.42/7.03  
% 51.42/7.03  inst_num_of_clauses:                    3099
% 51.42/7.03  inst_num_in_passive:                    718
% 51.42/7.03  inst_num_in_active:                     4566
% 51.42/7.03  inst_num_in_unprocessed:                37
% 51.42/7.03  inst_num_of_loops:                      5499
% 51.42/7.03  inst_num_of_learning_restarts:          1
% 51.42/7.03  inst_num_moves_active_passive:          918
% 51.42/7.03  inst_lit_activity:                      0
% 51.42/7.03  inst_lit_activity_moves:                0
% 51.42/7.03  inst_num_tautologies:                   0
% 51.42/7.03  inst_num_prop_implied:                  0
% 51.42/7.03  inst_num_existing_simplified:           0
% 51.42/7.03  inst_num_eq_res_simplified:             0
% 51.42/7.03  inst_num_child_elim:                    0
% 51.42/7.03  inst_num_of_dismatching_blockings:      17352
% 51.42/7.03  inst_num_of_non_proper_insts:           18183
% 51.42/7.03  inst_num_of_duplicates:                 0
% 51.42/7.03  inst_inst_num_from_inst_to_res:         0
% 51.42/7.03  inst_dismatching_checking_time:         0.
% 51.42/7.03  
% 51.42/7.03  ------ Resolution
% 51.42/7.03  
% 51.42/7.03  res_num_of_clauses:                     51
% 51.42/7.03  res_num_in_passive:                     51
% 51.42/7.03  res_num_in_active:                      0
% 51.42/7.03  res_num_of_loops:                       173
% 51.42/7.03  res_forward_subset_subsumed:            379
% 51.42/7.03  res_backward_subset_subsumed:           6
% 51.42/7.03  res_forward_subsumed:                   0
% 51.42/7.03  res_backward_subsumed:                  0
% 51.42/7.03  res_forward_subsumption_resolution:     6
% 51.42/7.03  res_backward_subsumption_resolution:    0
% 51.42/7.03  res_clause_to_clause_subsumption:       62668
% 51.42/7.03  res_orphan_elimination:                 0
% 51.42/7.03  res_tautology_del:                      1034
% 51.42/7.03  res_num_eq_res_simplified:              0
% 51.42/7.03  res_num_sel_changes:                    0
% 51.42/7.03  res_moves_from_active_to_pass:          0
% 51.42/7.03  
% 51.42/7.03  ------ Superposition
% 51.42/7.03  
% 51.42/7.03  sup_time_total:                         0.
% 51.42/7.03  sup_time_generating:                    0.
% 51.42/7.03  sup_time_sim_full:                      0.
% 51.42/7.03  sup_time_sim_immed:                     0.
% 51.42/7.03  
% 51.42/7.03  sup_num_of_clauses:                     8292
% 51.42/7.03  sup_num_in_active:                      71
% 51.42/7.03  sup_num_in_passive:                     8221
% 51.42/7.03  sup_num_of_loops:                       1099
% 51.42/7.03  sup_fw_superposition:                   5342
% 51.42/7.03  sup_bw_superposition:                   6450
% 51.42/7.03  sup_immediate_simplified:               5889
% 51.42/7.03  sup_given_eliminated:                   3
% 51.42/7.03  comparisons_done:                       0
% 51.42/7.03  comparisons_avoided:                    3
% 51.42/7.03  
% 51.42/7.03  ------ Simplifications
% 51.42/7.03  
% 51.42/7.03  
% 51.42/7.03  sim_fw_subset_subsumed:                 446
% 51.42/7.03  sim_bw_subset_subsumed:                 307
% 51.42/7.03  sim_fw_subsumed:                        59
% 51.42/7.03  sim_bw_subsumed:                        6
% 51.42/7.03  sim_fw_subsumption_res:                 0
% 51.42/7.03  sim_bw_subsumption_res:                 0
% 51.42/7.03  sim_tautology_del:                      4
% 51.42/7.03  sim_eq_tautology_del:                   543
% 51.42/7.03  sim_eq_res_simp:                        3
% 51.42/7.03  sim_fw_demodulated:                     1076
% 51.42/7.03  sim_bw_demodulated:                     1026
% 51.42/7.03  sim_light_normalised:                   4884
% 51.42/7.03  sim_joinable_taut:                      0
% 51.42/7.03  sim_joinable_simp:                      0
% 51.42/7.03  sim_ac_normalised:                      0
% 51.42/7.03  sim_smt_subsumption:                    0
% 51.42/7.03  
%------------------------------------------------------------------------------
