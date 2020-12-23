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
% DateTime   : Thu Dec  3 12:07:09 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 733 expanded)
%              Number of clauses        :  117 ( 232 expanded)
%              Number of leaves         :   23 ( 169 expanded)
%              Depth                    :   23
%              Number of atoms          :  779 (4561 expanded)
%              Number of equality atoms :  249 ( 380 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK4,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK4,X0,X0)
        & v1_funct_2(sK4,X0,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
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
          ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v3_funct_2(X2,sK2,sK2)
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK3,sK2,sK2)
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK3,sK2,sK2)
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f67,f77,f76])).

fof(f127,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f78])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f78])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f121,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f26,axiom,(
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

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f118,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f120,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f123,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f124,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f126,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f78])).

fof(f128,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f78])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f22,axiom,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f74,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3))
        & r2_hidden(sK1(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3))
            & r2_hidden(sK1(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f74])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK1(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f125,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f60])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2590,plain,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2585,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_24,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_682,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_694,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_682,c_13])).

cnf(c_725,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_694])).

cnf(c_726,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_2579,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_6596,plain,
    ( k2_relat_1(sK3) = sK2
    | v3_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_2579])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_46,negated_conjecture,
    ( v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3101,plain,
    ( ~ v3_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_3103,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_3101])).

cnf(c_7490,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6596,c_48,c_46,c_45,c_3103])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2608,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6827,plain,
    ( k2_relset_1(sK2,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2585,c_2608])).

cnf(c_7493,plain,
    ( k2_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_7490,c_6827])).

cnf(c_38,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2592,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8056,plain,
    ( k2_funct_1(sK3) = X0
    | sK2 = k1_xboole_0
    | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
    | v1_funct_2(X0,sK2,sK2) != iProver_top
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7493,c_2592])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_51,plain,
    ( v3_funct_2(sK3,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_53,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_54,plain,
    ( v1_funct_2(sK4,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_56,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_58,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_25,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3062,plain,
    ( ~ v3_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3063,plain,
    ( v3_funct_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3062])).

cnf(c_3065,plain,
    ( v3_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3063])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3091,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ v3_funct_2(sK3,X0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3092,plain,
    ( v1_funct_2(sK3,X0,X0) != iProver_top
    | v3_funct_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3091])).

cnf(c_3094,plain,
    ( v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v3_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(k2_funct_2(sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3092])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3166,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ v3_funct_2(sK3,X0,X0)
    | m1_subset_1(k2_funct_2(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3167,plain,
    ( v1_funct_2(sK3,X0,X0) != iProver_top
    | v3_funct_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(k2_funct_2(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3166])).

cnf(c_3169,plain,
    ( v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v3_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3167])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3186,plain,
    ( v1_funct_2(k2_funct_2(X0,sK3),X0,X0)
    | ~ v1_funct_2(sK3,X0,X0)
    | ~ v3_funct_2(sK3,X0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3187,plain,
    ( v1_funct_2(k2_funct_2(X0,sK3),X0,X0) = iProver_top
    | v1_funct_2(sK3,X0,X0) != iProver_top
    | v3_funct_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_3189,plain,
    ( v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2) = iProver_top
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v3_funct_2(sK3,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3187])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK1(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_770,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_xboole_0(X4)
    | X0 != X4
    | sK1(X0,X2,X3) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_37])).

cnf(c_771,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_3225,plain,
    ( r2_relset_1(X0,X1,sK4,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_4479,plain,
    ( r2_relset_1(X0,X1,sK4,k2_funct_2(X2,sK3))
    | ~ v1_funct_2(k2_funct_2(X2,sK3),X0,X1)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(k2_funct_2(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k2_funct_2(X2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_4480,plain,
    ( r2_relset_1(X0,X1,sK4,k2_funct_2(X2,sK3)) = iProver_top
    | v1_funct_2(k2_funct_2(X2,sK3),X0,X1) != iProver_top
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_2(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_2(X2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4479])).

cnf(c_4482,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) = iProver_top
    | v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(k2_funct_2(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4480])).

cnf(c_2589,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6595,plain,
    ( k2_relat_1(sK4) = sK2
    | v3_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2579])).

cnf(c_42,negated_conjecture,
    ( v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3096,plain,
    ( ~ v3_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_3098,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4)
    | k2_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_3096])).

cnf(c_7480,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6595,c_44,c_42,c_41,c_3098])).

cnf(c_2609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5242,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2609])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2613,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5866,plain,
    ( k2_xboole_0(k1_relat_1(sK4),k2_relat_1(sK4)) = k3_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5242,c_2613])).

cnf(c_7484,plain,
    ( k2_xboole_0(k1_relat_1(sK4),sK2) = k3_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_7480,c_5866])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_8])).

cnf(c_665,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_13])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_2580,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_6575,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2580])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2616,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7078,plain,
    ( k2_xboole_0(k1_relat_1(sK4),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_6575,c_2616])).

cnf(c_8060,plain,
    ( k3_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7484,c_7078])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7669,plain,
    ( r1_tarski(k3_relat_1(sK4),k2_xboole_0(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2589,c_2604])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7675,plain,
    ( r1_tarski(k3_relat_1(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7669,c_0])).

cnf(c_8062,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8060,c_7675])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2615,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8070,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8062,c_2615])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_625,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_2581,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_26079,plain,
    ( sK2 != k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8070,c_2581])).

cnf(c_31702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | k2_funct_1(sK3) = X0
    | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
    | v1_funct_2(X0,sK2,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8056,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_58,c_3065,c_3094,c_3169,c_3189,c_4482,c_8062,c_26079])).

cnf(c_31703,plain,
    ( k2_funct_1(sK3) = X0
    | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
    | v1_funct_2(X0,sK2,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_31702])).

cnf(c_31713,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2590,c_31703])).

cnf(c_32136,plain,
    ( k2_funct_1(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31713,c_53,c_54,c_56])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2594,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9525,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v3_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_2594])).

cnf(c_3131,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ v3_funct_2(sK3,X0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK3)
    | k2_funct_2(X0,sK3) = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3133,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3131])).

cnf(c_10939,plain,
    ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9525,c_48,c_47,c_46,c_45,c_3133])).

cnf(c_2591,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10942,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10939,c_2591])).

cnf(c_32170,plain,
    ( r2_relset_1(sK2,sK2,sK4,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32136,c_10942])).

cnf(c_17,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3051,plain,
    ( r2_relset_1(sK2,sK2,sK4,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3052,plain,
    ( r2_relset_1(sK2,sK2,sK4,sK4) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3051])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32170,c_3052,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:44:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.41/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/1.98  
% 11.41/1.98  ------  iProver source info
% 11.41/1.98  
% 11.41/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.41/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/1.98  git: non_committed_changes: false
% 11.41/1.98  git: last_make_outside_of_git: false
% 11.41/1.98  
% 11.41/1.98  ------ 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options
% 11.41/1.98  
% 11.41/1.98  --out_options                           all
% 11.41/1.98  --tptp_safe_out                         true
% 11.41/1.98  --problem_path                          ""
% 11.41/1.98  --include_path                          ""
% 11.41/1.98  --clausifier                            res/vclausify_rel
% 11.41/1.98  --clausifier_options                    --mode clausify
% 11.41/1.98  --stdin                                 false
% 11.41/1.98  --stats_out                             all
% 11.41/1.98  
% 11.41/1.98  ------ General Options
% 11.41/1.98  
% 11.41/1.98  --fof                                   false
% 11.41/1.98  --time_out_real                         305.
% 11.41/1.98  --time_out_virtual                      -1.
% 11.41/1.98  --symbol_type_check                     false
% 11.41/1.98  --clausify_out                          false
% 11.41/1.98  --sig_cnt_out                           false
% 11.41/1.98  --trig_cnt_out                          false
% 11.41/1.98  --trig_cnt_out_tolerance                1.
% 11.41/1.98  --trig_cnt_out_sk_spl                   false
% 11.41/1.98  --abstr_cl_out                          false
% 11.41/1.98  
% 11.41/1.98  ------ Global Options
% 11.41/1.98  
% 11.41/1.98  --schedule                              default
% 11.41/1.98  --add_important_lit                     false
% 11.41/1.98  --prop_solver_per_cl                    1000
% 11.41/1.98  --min_unsat_core                        false
% 11.41/1.98  --soft_assumptions                      false
% 11.41/1.98  --soft_lemma_size                       3
% 11.41/1.98  --prop_impl_unit_size                   0
% 11.41/1.98  --prop_impl_unit                        []
% 11.41/1.98  --share_sel_clauses                     true
% 11.41/1.98  --reset_solvers                         false
% 11.41/1.98  --bc_imp_inh                            [conj_cone]
% 11.41/1.98  --conj_cone_tolerance                   3.
% 11.41/1.98  --extra_neg_conj                        none
% 11.41/1.98  --large_theory_mode                     true
% 11.41/1.98  --prolific_symb_bound                   200
% 11.41/1.98  --lt_threshold                          2000
% 11.41/1.98  --clause_weak_htbl                      true
% 11.41/1.98  --gc_record_bc_elim                     false
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing Options
% 11.41/1.98  
% 11.41/1.98  --preprocessing_flag                    true
% 11.41/1.98  --time_out_prep_mult                    0.1
% 11.41/1.98  --splitting_mode                        input
% 11.41/1.98  --splitting_grd                         true
% 11.41/1.98  --splitting_cvd                         false
% 11.41/1.98  --splitting_cvd_svl                     false
% 11.41/1.98  --splitting_nvd                         32
% 11.41/1.98  --sub_typing                            true
% 11.41/1.98  --prep_gs_sim                           true
% 11.41/1.98  --prep_unflatten                        true
% 11.41/1.98  --prep_res_sim                          true
% 11.41/1.98  --prep_upred                            true
% 11.41/1.98  --prep_sem_filter                       exhaustive
% 11.41/1.98  --prep_sem_filter_out                   false
% 11.41/1.98  --pred_elim                             true
% 11.41/1.98  --res_sim_input                         true
% 11.41/1.98  --eq_ax_congr_red                       true
% 11.41/1.98  --pure_diseq_elim                       true
% 11.41/1.98  --brand_transform                       false
% 11.41/1.98  --non_eq_to_eq                          false
% 11.41/1.98  --prep_def_merge                        true
% 11.41/1.98  --prep_def_merge_prop_impl              false
% 11.41/1.98  --prep_def_merge_mbd                    true
% 11.41/1.98  --prep_def_merge_tr_red                 false
% 11.41/1.98  --prep_def_merge_tr_cl                  false
% 11.41/1.98  --smt_preprocessing                     true
% 11.41/1.98  --smt_ac_axioms                         fast
% 11.41/1.98  --preprocessed_out                      false
% 11.41/1.98  --preprocessed_stats                    false
% 11.41/1.98  
% 11.41/1.98  ------ Abstraction refinement Options
% 11.41/1.98  
% 11.41/1.98  --abstr_ref                             []
% 11.41/1.98  --abstr_ref_prep                        false
% 11.41/1.98  --abstr_ref_until_sat                   false
% 11.41/1.98  --abstr_ref_sig_restrict                funpre
% 11.41/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.98  --abstr_ref_under                       []
% 11.41/1.98  
% 11.41/1.98  ------ SAT Options
% 11.41/1.98  
% 11.41/1.98  --sat_mode                              false
% 11.41/1.98  --sat_fm_restart_options                ""
% 11.41/1.98  --sat_gr_def                            false
% 11.41/1.98  --sat_epr_types                         true
% 11.41/1.98  --sat_non_cyclic_types                  false
% 11.41/1.98  --sat_finite_models                     false
% 11.41/1.98  --sat_fm_lemmas                         false
% 11.41/1.98  --sat_fm_prep                           false
% 11.41/1.98  --sat_fm_uc_incr                        true
% 11.41/1.98  --sat_out_model                         small
% 11.41/1.98  --sat_out_clauses                       false
% 11.41/1.98  
% 11.41/1.98  ------ QBF Options
% 11.41/1.98  
% 11.41/1.98  --qbf_mode                              false
% 11.41/1.98  --qbf_elim_univ                         false
% 11.41/1.98  --qbf_dom_inst                          none
% 11.41/1.98  --qbf_dom_pre_inst                      false
% 11.41/1.98  --qbf_sk_in                             false
% 11.41/1.98  --qbf_pred_elim                         true
% 11.41/1.98  --qbf_split                             512
% 11.41/1.98  
% 11.41/1.98  ------ BMC1 Options
% 11.41/1.98  
% 11.41/1.98  --bmc1_incremental                      false
% 11.41/1.98  --bmc1_axioms                           reachable_all
% 11.41/1.98  --bmc1_min_bound                        0
% 11.41/1.98  --bmc1_max_bound                        -1
% 11.41/1.98  --bmc1_max_bound_default                -1
% 11.41/1.98  --bmc1_symbol_reachability              true
% 11.41/1.98  --bmc1_property_lemmas                  false
% 11.41/1.98  --bmc1_k_induction                      false
% 11.41/1.98  --bmc1_non_equiv_states                 false
% 11.41/1.98  --bmc1_deadlock                         false
% 11.41/1.98  --bmc1_ucm                              false
% 11.41/1.98  --bmc1_add_unsat_core                   none
% 11.41/1.98  --bmc1_unsat_core_children              false
% 11.41/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.98  --bmc1_out_stat                         full
% 11.41/1.98  --bmc1_ground_init                      false
% 11.41/1.98  --bmc1_pre_inst_next_state              false
% 11.41/1.98  --bmc1_pre_inst_state                   false
% 11.41/1.98  --bmc1_pre_inst_reach_state             false
% 11.41/1.98  --bmc1_out_unsat_core                   false
% 11.41/1.98  --bmc1_aig_witness_out                  false
% 11.41/1.98  --bmc1_verbose                          false
% 11.41/1.98  --bmc1_dump_clauses_tptp                false
% 11.41/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.98  --bmc1_dump_file                        -
% 11.41/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.98  --bmc1_ucm_extend_mode                  1
% 11.41/1.98  --bmc1_ucm_init_mode                    2
% 11.41/1.98  --bmc1_ucm_cone_mode                    none
% 11.41/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.98  --bmc1_ucm_relax_model                  4
% 11.41/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.98  --bmc1_ucm_layered_model                none
% 11.41/1.98  --bmc1_ucm_max_lemma_size               10
% 11.41/1.98  
% 11.41/1.98  ------ AIG Options
% 11.41/1.98  
% 11.41/1.98  --aig_mode                              false
% 11.41/1.98  
% 11.41/1.98  ------ Instantiation Options
% 11.41/1.98  
% 11.41/1.98  --instantiation_flag                    true
% 11.41/1.98  --inst_sos_flag                         false
% 11.41/1.98  --inst_sos_phase                        true
% 11.41/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel_side                     num_symb
% 11.41/1.98  --inst_solver_per_active                1400
% 11.41/1.98  --inst_solver_calls_frac                1.
% 11.41/1.98  --inst_passive_queue_type               priority_queues
% 11.41/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.98  --inst_passive_queues_freq              [25;2]
% 11.41/1.98  --inst_dismatching                      true
% 11.41/1.98  --inst_eager_unprocessed_to_passive     true
% 11.41/1.98  --inst_prop_sim_given                   true
% 11.41/1.98  --inst_prop_sim_new                     false
% 11.41/1.98  --inst_subs_new                         false
% 11.41/1.98  --inst_eq_res_simp                      false
% 11.41/1.98  --inst_subs_given                       false
% 11.41/1.98  --inst_orphan_elimination               true
% 11.41/1.98  --inst_learning_loop_flag               true
% 11.41/1.98  --inst_learning_start                   3000
% 11.41/1.98  --inst_learning_factor                  2
% 11.41/1.98  --inst_start_prop_sim_after_learn       3
% 11.41/1.98  --inst_sel_renew                        solver
% 11.41/1.98  --inst_lit_activity_flag                true
% 11.41/1.98  --inst_restr_to_given                   false
% 11.41/1.98  --inst_activity_threshold               500
% 11.41/1.98  --inst_out_proof                        true
% 11.41/1.98  
% 11.41/1.98  ------ Resolution Options
% 11.41/1.98  
% 11.41/1.98  --resolution_flag                       true
% 11.41/1.98  --res_lit_sel                           adaptive
% 11.41/1.98  --res_lit_sel_side                      none
% 11.41/1.98  --res_ordering                          kbo
% 11.41/1.98  --res_to_prop_solver                    active
% 11.41/1.98  --res_prop_simpl_new                    false
% 11.41/1.98  --res_prop_simpl_given                  true
% 11.41/1.98  --res_passive_queue_type                priority_queues
% 11.41/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.98  --res_passive_queues_freq               [15;5]
% 11.41/1.98  --res_forward_subs                      full
% 11.41/1.98  --res_backward_subs                     full
% 11.41/1.98  --res_forward_subs_resolution           true
% 11.41/1.98  --res_backward_subs_resolution          true
% 11.41/1.98  --res_orphan_elimination                true
% 11.41/1.98  --res_time_limit                        2.
% 11.41/1.98  --res_out_proof                         true
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Options
% 11.41/1.98  
% 11.41/1.98  --superposition_flag                    true
% 11.41/1.98  --sup_passive_queue_type                priority_queues
% 11.41/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.98  --demod_completeness_check              fast
% 11.41/1.98  --demod_use_ground                      true
% 11.41/1.98  --sup_to_prop_solver                    passive
% 11.41/1.98  --sup_prop_simpl_new                    true
% 11.41/1.98  --sup_prop_simpl_given                  true
% 11.41/1.98  --sup_fun_splitting                     false
% 11.41/1.98  --sup_smt_interval                      50000
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Simplification Setup
% 11.41/1.98  
% 11.41/1.98  --sup_indices_passive                   []
% 11.41/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_full_bw                           [BwDemod]
% 11.41/1.98  --sup_immed_triv                        [TrivRules]
% 11.41/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_immed_bw_main                     []
% 11.41/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  
% 11.41/1.98  ------ Combination Options
% 11.41/1.98  
% 11.41/1.98  --comb_res_mult                         3
% 11.41/1.98  --comb_sup_mult                         2
% 11.41/1.98  --comb_inst_mult                        10
% 11.41/1.98  
% 11.41/1.98  ------ Debug Options
% 11.41/1.98  
% 11.41/1.98  --dbg_backtrace                         false
% 11.41/1.98  --dbg_dump_prop_clauses                 false
% 11.41/1.98  --dbg_dump_prop_clauses_file            -
% 11.41/1.98  --dbg_out_stat                          false
% 11.41/1.98  ------ Parsing...
% 11.41/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.41/1.98  ------ Proving...
% 11.41/1.98  ------ Problem Properties 
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  clauses                                 41
% 11.41/1.98  conjectures                             10
% 11.41/1.98  EPR                                     6
% 11.41/1.98  Horn                                    40
% 11.41/1.98  unary                                   12
% 11.41/1.98  binary                                  9
% 11.41/1.98  lits                                    131
% 11.41/1.98  lits eq                                 17
% 11.41/1.98  fd_pure                                 0
% 11.41/1.98  fd_pseudo                               0
% 11.41/1.98  fd_cond                                 0
% 11.41/1.98  fd_pseudo_cond                          3
% 11.41/1.98  AC symbols                              0
% 11.41/1.98  
% 11.41/1.98  ------ Schedule dynamic 5 is on 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  ------ 
% 11.41/1.98  Current options:
% 11.41/1.98  ------ 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options
% 11.41/1.98  
% 11.41/1.98  --out_options                           all
% 11.41/1.98  --tptp_safe_out                         true
% 11.41/1.98  --problem_path                          ""
% 11.41/1.98  --include_path                          ""
% 11.41/1.98  --clausifier                            res/vclausify_rel
% 11.41/1.98  --clausifier_options                    --mode clausify
% 11.41/1.98  --stdin                                 false
% 11.41/1.98  --stats_out                             all
% 11.41/1.98  
% 11.41/1.98  ------ General Options
% 11.41/1.98  
% 11.41/1.98  --fof                                   false
% 11.41/1.98  --time_out_real                         305.
% 11.41/1.98  --time_out_virtual                      -1.
% 11.41/1.98  --symbol_type_check                     false
% 11.41/1.98  --clausify_out                          false
% 11.41/1.98  --sig_cnt_out                           false
% 11.41/1.98  --trig_cnt_out                          false
% 11.41/1.98  --trig_cnt_out_tolerance                1.
% 11.41/1.98  --trig_cnt_out_sk_spl                   false
% 11.41/1.98  --abstr_cl_out                          false
% 11.41/1.98  
% 11.41/1.98  ------ Global Options
% 11.41/1.98  
% 11.41/1.98  --schedule                              default
% 11.41/1.98  --add_important_lit                     false
% 11.41/1.98  --prop_solver_per_cl                    1000
% 11.41/1.98  --min_unsat_core                        false
% 11.41/1.98  --soft_assumptions                      false
% 11.41/1.98  --soft_lemma_size                       3
% 11.41/1.98  --prop_impl_unit_size                   0
% 11.41/1.98  --prop_impl_unit                        []
% 11.41/1.98  --share_sel_clauses                     true
% 11.41/1.98  --reset_solvers                         false
% 11.41/1.98  --bc_imp_inh                            [conj_cone]
% 11.41/1.98  --conj_cone_tolerance                   3.
% 11.41/1.98  --extra_neg_conj                        none
% 11.41/1.98  --large_theory_mode                     true
% 11.41/1.98  --prolific_symb_bound                   200
% 11.41/1.98  --lt_threshold                          2000
% 11.41/1.98  --clause_weak_htbl                      true
% 11.41/1.98  --gc_record_bc_elim                     false
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing Options
% 11.41/1.98  
% 11.41/1.98  --preprocessing_flag                    true
% 11.41/1.98  --time_out_prep_mult                    0.1
% 11.41/1.98  --splitting_mode                        input
% 11.41/1.98  --splitting_grd                         true
% 11.41/1.98  --splitting_cvd                         false
% 11.41/1.98  --splitting_cvd_svl                     false
% 11.41/1.98  --splitting_nvd                         32
% 11.41/1.98  --sub_typing                            true
% 11.41/1.98  --prep_gs_sim                           true
% 11.41/1.98  --prep_unflatten                        true
% 11.41/1.98  --prep_res_sim                          true
% 11.41/1.98  --prep_upred                            true
% 11.41/1.98  --prep_sem_filter                       exhaustive
% 11.41/1.98  --prep_sem_filter_out                   false
% 11.41/1.98  --pred_elim                             true
% 11.41/1.98  --res_sim_input                         true
% 11.41/1.98  --eq_ax_congr_red                       true
% 11.41/1.98  --pure_diseq_elim                       true
% 11.41/1.98  --brand_transform                       false
% 11.41/1.98  --non_eq_to_eq                          false
% 11.41/1.98  --prep_def_merge                        true
% 11.41/1.98  --prep_def_merge_prop_impl              false
% 11.41/1.98  --prep_def_merge_mbd                    true
% 11.41/1.98  --prep_def_merge_tr_red                 false
% 11.41/1.98  --prep_def_merge_tr_cl                  false
% 11.41/1.98  --smt_preprocessing                     true
% 11.41/1.98  --smt_ac_axioms                         fast
% 11.41/1.98  --preprocessed_out                      false
% 11.41/1.98  --preprocessed_stats                    false
% 11.41/1.98  
% 11.41/1.98  ------ Abstraction refinement Options
% 11.41/1.98  
% 11.41/1.98  --abstr_ref                             []
% 11.41/1.98  --abstr_ref_prep                        false
% 11.41/1.98  --abstr_ref_until_sat                   false
% 11.41/1.98  --abstr_ref_sig_restrict                funpre
% 11.41/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.98  --abstr_ref_under                       []
% 11.41/1.98  
% 11.41/1.98  ------ SAT Options
% 11.41/1.98  
% 11.41/1.98  --sat_mode                              false
% 11.41/1.98  --sat_fm_restart_options                ""
% 11.41/1.98  --sat_gr_def                            false
% 11.41/1.98  --sat_epr_types                         true
% 11.41/1.98  --sat_non_cyclic_types                  false
% 11.41/1.98  --sat_finite_models                     false
% 11.41/1.98  --sat_fm_lemmas                         false
% 11.41/1.98  --sat_fm_prep                           false
% 11.41/1.98  --sat_fm_uc_incr                        true
% 11.41/1.98  --sat_out_model                         small
% 11.41/1.98  --sat_out_clauses                       false
% 11.41/1.98  
% 11.41/1.98  ------ QBF Options
% 11.41/1.98  
% 11.41/1.98  --qbf_mode                              false
% 11.41/1.98  --qbf_elim_univ                         false
% 11.41/1.98  --qbf_dom_inst                          none
% 11.41/1.98  --qbf_dom_pre_inst                      false
% 11.41/1.98  --qbf_sk_in                             false
% 11.41/1.98  --qbf_pred_elim                         true
% 11.41/1.98  --qbf_split                             512
% 11.41/1.98  
% 11.41/1.98  ------ BMC1 Options
% 11.41/1.98  
% 11.41/1.98  --bmc1_incremental                      false
% 11.41/1.98  --bmc1_axioms                           reachable_all
% 11.41/1.98  --bmc1_min_bound                        0
% 11.41/1.98  --bmc1_max_bound                        -1
% 11.41/1.98  --bmc1_max_bound_default                -1
% 11.41/1.98  --bmc1_symbol_reachability              true
% 11.41/1.98  --bmc1_property_lemmas                  false
% 11.41/1.98  --bmc1_k_induction                      false
% 11.41/1.98  --bmc1_non_equiv_states                 false
% 11.41/1.98  --bmc1_deadlock                         false
% 11.41/1.98  --bmc1_ucm                              false
% 11.41/1.98  --bmc1_add_unsat_core                   none
% 11.41/1.98  --bmc1_unsat_core_children              false
% 11.41/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.98  --bmc1_out_stat                         full
% 11.41/1.98  --bmc1_ground_init                      false
% 11.41/1.98  --bmc1_pre_inst_next_state              false
% 11.41/1.98  --bmc1_pre_inst_state                   false
% 11.41/1.98  --bmc1_pre_inst_reach_state             false
% 11.41/1.98  --bmc1_out_unsat_core                   false
% 11.41/1.98  --bmc1_aig_witness_out                  false
% 11.41/1.98  --bmc1_verbose                          false
% 11.41/1.98  --bmc1_dump_clauses_tptp                false
% 11.41/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.98  --bmc1_dump_file                        -
% 11.41/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.98  --bmc1_ucm_extend_mode                  1
% 11.41/1.98  --bmc1_ucm_init_mode                    2
% 11.41/1.98  --bmc1_ucm_cone_mode                    none
% 11.41/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.98  --bmc1_ucm_relax_model                  4
% 11.41/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.98  --bmc1_ucm_layered_model                none
% 11.41/1.98  --bmc1_ucm_max_lemma_size               10
% 11.41/1.98  
% 11.41/1.98  ------ AIG Options
% 11.41/1.98  
% 11.41/1.98  --aig_mode                              false
% 11.41/1.98  
% 11.41/1.98  ------ Instantiation Options
% 11.41/1.98  
% 11.41/1.98  --instantiation_flag                    true
% 11.41/1.98  --inst_sos_flag                         false
% 11.41/1.98  --inst_sos_phase                        true
% 11.41/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel_side                     none
% 11.41/1.98  --inst_solver_per_active                1400
% 11.41/1.98  --inst_solver_calls_frac                1.
% 11.41/1.98  --inst_passive_queue_type               priority_queues
% 11.41/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.98  --inst_passive_queues_freq              [25;2]
% 11.41/1.98  --inst_dismatching                      true
% 11.41/1.98  --inst_eager_unprocessed_to_passive     true
% 11.41/1.98  --inst_prop_sim_given                   true
% 11.41/1.98  --inst_prop_sim_new                     false
% 11.41/1.98  --inst_subs_new                         false
% 11.41/1.98  --inst_eq_res_simp                      false
% 11.41/1.98  --inst_subs_given                       false
% 11.41/1.98  --inst_orphan_elimination               true
% 11.41/1.98  --inst_learning_loop_flag               true
% 11.41/1.98  --inst_learning_start                   3000
% 11.41/1.98  --inst_learning_factor                  2
% 11.41/1.98  --inst_start_prop_sim_after_learn       3
% 11.41/1.98  --inst_sel_renew                        solver
% 11.41/1.98  --inst_lit_activity_flag                true
% 11.41/1.98  --inst_restr_to_given                   false
% 11.41/1.98  --inst_activity_threshold               500
% 11.41/1.98  --inst_out_proof                        true
% 11.41/1.98  
% 11.41/1.98  ------ Resolution Options
% 11.41/1.98  
% 11.41/1.98  --resolution_flag                       false
% 11.41/1.98  --res_lit_sel                           adaptive
% 11.41/1.98  --res_lit_sel_side                      none
% 11.41/1.98  --res_ordering                          kbo
% 11.41/1.98  --res_to_prop_solver                    active
% 11.41/1.98  --res_prop_simpl_new                    false
% 11.41/1.98  --res_prop_simpl_given                  true
% 11.41/1.98  --res_passive_queue_type                priority_queues
% 11.41/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.98  --res_passive_queues_freq               [15;5]
% 11.41/1.98  --res_forward_subs                      full
% 11.41/1.98  --res_backward_subs                     full
% 11.41/1.98  --res_forward_subs_resolution           true
% 11.41/1.98  --res_backward_subs_resolution          true
% 11.41/1.98  --res_orphan_elimination                true
% 11.41/1.98  --res_time_limit                        2.
% 11.41/1.98  --res_out_proof                         true
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Options
% 11.41/1.98  
% 11.41/1.98  --superposition_flag                    true
% 11.41/1.98  --sup_passive_queue_type                priority_queues
% 11.41/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.98  --demod_completeness_check              fast
% 11.41/1.98  --demod_use_ground                      true
% 11.41/1.98  --sup_to_prop_solver                    passive
% 11.41/1.98  --sup_prop_simpl_new                    true
% 11.41/1.98  --sup_prop_simpl_given                  true
% 11.41/1.98  --sup_fun_splitting                     false
% 11.41/1.98  --sup_smt_interval                      50000
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Simplification Setup
% 11.41/1.98  
% 11.41/1.98  --sup_indices_passive                   []
% 11.41/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_full_bw                           [BwDemod]
% 11.41/1.98  --sup_immed_triv                        [TrivRules]
% 11.41/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_immed_bw_main                     []
% 11.41/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  
% 11.41/1.98  ------ Combination Options
% 11.41/1.98  
% 11.41/1.98  --comb_res_mult                         3
% 11.41/1.98  --comb_sup_mult                         2
% 11.41/1.98  --comb_inst_mult                        10
% 11.41/1.98  
% 11.41/1.98  ------ Debug Options
% 11.41/1.98  
% 11.41/1.98  --dbg_backtrace                         false
% 11.41/1.98  --dbg_dump_prop_clauses                 false
% 11.41/1.98  --dbg_dump_prop_clauses_file            -
% 11.41/1.98  --dbg_out_stat                          false
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  ------ Proving...
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  % SZS status Theorem for theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  fof(f27,conjecture,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f28,negated_conjecture,(
% 11.41/1.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 11.41/1.98    inference(negated_conjecture,[],[f27])).
% 11.41/1.98  
% 11.41/1.98  fof(f66,plain,(
% 11.41/1.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 11.41/1.98    inference(ennf_transformation,[],[f28])).
% 11.41/1.98  
% 11.41/1.98  fof(f67,plain,(
% 11.41/1.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 11.41/1.98    inference(flattening,[],[f66])).
% 11.41/1.98  
% 11.41/1.98  fof(f77,plain,(
% 11.41/1.98    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK4,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK4,X0,X0) & v1_funct_2(sK4,X0,X0) & v1_funct_1(sK4))) )),
% 11.41/1.98    introduced(choice_axiom,[])).
% 11.41/1.98  
% 11.41/1.98  fof(f76,plain,(
% 11.41/1.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 11.41/1.98    introduced(choice_axiom,[])).
% 11.41/1.98  
% 11.41/1.98  fof(f78,plain,(
% 11.41/1.98    (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 11.41/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f67,f77,f76])).
% 11.41/1.98  
% 11.41/1.98  fof(f127,plain,(
% 11.41/1.98    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f122,plain,(
% 11.41/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f19,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f52,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(ennf_transformation,[],[f19])).
% 11.41/1.98  
% 11.41/1.98  fof(f53,plain,(
% 11.41/1.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(flattening,[],[f52])).
% 11.41/1.98  
% 11.41/1.98  fof(f105,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f53])).
% 11.41/1.98  
% 11.41/1.98  fof(f12,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f43,plain,(
% 11.41/1.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(ennf_transformation,[],[f12])).
% 11.41/1.98  
% 11.41/1.98  fof(f94,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f43])).
% 11.41/1.98  
% 11.41/1.98  fof(f20,axiom,(
% 11.41/1.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f54,plain,(
% 11.41/1.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.41/1.98    inference(ennf_transformation,[],[f20])).
% 11.41/1.98  
% 11.41/1.98  fof(f55,plain,(
% 11.41/1.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.41/1.98    inference(flattening,[],[f54])).
% 11.41/1.98  
% 11.41/1.98  fof(f73,plain,(
% 11.41/1.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.41/1.98    inference(nnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  fof(f106,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f73])).
% 11.41/1.98  
% 11.41/1.98  fof(f11,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f42,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(ennf_transformation,[],[f11])).
% 11.41/1.98  
% 11.41/1.98  fof(f92,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f42])).
% 11.41/1.98  
% 11.41/1.98  fof(f119,plain,(
% 11.41/1.98    v1_funct_1(sK3)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f121,plain,(
% 11.41/1.98    v3_funct_2(sK3,sK2,sK2)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f13,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f44,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(ennf_transformation,[],[f13])).
% 11.41/1.98  
% 11.41/1.98  fof(f95,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f44])).
% 11.41/1.98  
% 11.41/1.98  fof(f26,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f64,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.41/1.98    inference(ennf_transformation,[],[f26])).
% 11.41/1.98  
% 11.41/1.98  fof(f65,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.41/1.98    inference(flattening,[],[f64])).
% 11.41/1.98  
% 11.41/1.98  fof(f118,plain,(
% 11.41/1.98    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f65])).
% 11.41/1.98  
% 11.41/1.98  fof(f120,plain,(
% 11.41/1.98    v1_funct_2(sK3,sK2,sK2)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f123,plain,(
% 11.41/1.98    v1_funct_1(sK4)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f124,plain,(
% 11.41/1.98    v1_funct_2(sK4,sK2,sK2)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f126,plain,(
% 11.41/1.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f128,plain,(
% 11.41/1.98    ~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f104,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f53])).
% 11.41/1.98  
% 11.41/1.98  fof(f22,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f58,plain,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.41/1.98    inference(ennf_transformation,[],[f22])).
% 11.41/1.98  
% 11.41/1.98  fof(f59,plain,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.41/1.98    inference(flattening,[],[f58])).
% 11.41/1.98  
% 11.41/1.98  fof(f110,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f59])).
% 11.41/1.98  
% 11.41/1.98  fof(f113,plain,(
% 11.41/1.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f59])).
% 11.41/1.98  
% 11.41/1.98  fof(f111,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f59])).
% 11.41/1.98  
% 11.41/1.98  fof(f5,axiom,(
% 11.41/1.98    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f34,plain,(
% 11.41/1.98    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 11.41/1.98    inference(ennf_transformation,[],[f5])).
% 11.41/1.98  
% 11.41/1.98  fof(f84,plain,(
% 11.41/1.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f34])).
% 11.41/1.98  
% 11.41/1.98  fof(f25,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f62,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.41/1.98    inference(ennf_transformation,[],[f25])).
% 11.41/1.98  
% 11.41/1.98  fof(f63,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.41/1.98    inference(flattening,[],[f62])).
% 11.41/1.98  
% 11.41/1.98  fof(f74,plain,(
% 11.41/1.98    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3)) & r2_hidden(sK1(X0,X2,X3),X0)))),
% 11.41/1.98    introduced(choice_axiom,[])).
% 11.41/1.98  
% 11.41/1.98  fof(f75,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | (k1_funct_1(X2,sK1(X0,X2,X3)) != k1_funct_1(X3,sK1(X0,X2,X3)) & r2_hidden(sK1(X0,X2,X3),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.41/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f74])).
% 11.41/1.98  
% 11.41/1.98  fof(f116,plain,(
% 11.41/1.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | r2_hidden(sK1(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f75])).
% 11.41/1.98  
% 11.41/1.98  fof(f125,plain,(
% 11.41/1.98    v3_funct_2(sK4,sK2,sK2)),
% 11.41/1.98    inference(cnf_transformation,[],[f78])).
% 11.41/1.98  
% 11.41/1.98  fof(f8,axiom,(
% 11.41/1.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f37,plain,(
% 11.41/1.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f8])).
% 11.41/1.98  
% 11.41/1.98  fof(f88,plain,(
% 11.41/1.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f37])).
% 11.41/1.98  
% 11.41/1.98  fof(f93,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f43])).
% 11.41/1.98  
% 11.41/1.98  fof(f7,axiom,(
% 11.41/1.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f36,plain,(
% 11.41/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.41/1.98    inference(ennf_transformation,[],[f7])).
% 11.41/1.98  
% 11.41/1.98  fof(f69,plain,(
% 11.41/1.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.41/1.98    inference(nnf_transformation,[],[f36])).
% 11.41/1.98  
% 11.41/1.98  fof(f86,plain,(
% 11.41/1.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f69])).
% 11.41/1.98  
% 11.41/1.98  fof(f2,axiom,(
% 11.41/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f31,plain,(
% 11.41/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.41/1.98    inference(ennf_transformation,[],[f2])).
% 11.41/1.98  
% 11.41/1.98  fof(f80,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f31])).
% 11.41/1.98  
% 11.41/1.98  fof(f16,axiom,(
% 11.41/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f49,plain,(
% 11.41/1.98    ! [X0,X1,X2] : (r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(ennf_transformation,[],[f16])).
% 11.41/1.98  
% 11.41/1.98  fof(f99,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f49])).
% 11.41/1.98  
% 11.41/1.98  fof(f1,axiom,(
% 11.41/1.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f29,plain,(
% 11.41/1.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.41/1.98    inference(rectify,[],[f1])).
% 11.41/1.98  
% 11.41/1.98  fof(f79,plain,(
% 11.41/1.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.41/1.98    inference(cnf_transformation,[],[f29])).
% 11.41/1.98  
% 11.41/1.98  fof(f3,axiom,(
% 11.41/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f68,plain,(
% 11.41/1.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.41/1.98    inference(nnf_transformation,[],[f3])).
% 11.41/1.98  
% 11.41/1.98  fof(f82,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f68])).
% 11.41/1.98  
% 11.41/1.98  fof(f6,axiom,(
% 11.41/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f30,plain,(
% 11.41/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 11.41/1.98    inference(unused_predicate_definition_removal,[],[f6])).
% 11.41/1.98  
% 11.41/1.98  fof(f35,plain,(
% 11.41/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 11.41/1.98    inference(ennf_transformation,[],[f30])).
% 11.41/1.98  
% 11.41/1.98  fof(f85,plain,(
% 11.41/1.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 11.41/1.98    inference(cnf_transformation,[],[f35])).
% 11.41/1.98  
% 11.41/1.98  fof(f4,axiom,(
% 11.41/1.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f32,plain,(
% 11.41/1.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 11.41/1.98    inference(ennf_transformation,[],[f4])).
% 11.41/1.98  
% 11.41/1.98  fof(f33,plain,(
% 11.41/1.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 11.41/1.98    inference(flattening,[],[f32])).
% 11.41/1.98  
% 11.41/1.98  fof(f83,plain,(
% 11.41/1.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f33])).
% 11.41/1.98  
% 11.41/1.98  fof(f23,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f60,plain,(
% 11.41/1.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.41/1.98    inference(ennf_transformation,[],[f23])).
% 11.41/1.98  
% 11.41/1.98  fof(f61,plain,(
% 11.41/1.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.41/1.98    inference(flattening,[],[f60])).
% 11.41/1.98  
% 11.41/1.98  fof(f114,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f61])).
% 11.41/1.98  
% 11.41/1.98  fof(f14,axiom,(
% 11.41/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f45,plain,(
% 11.41/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.41/1.98    inference(ennf_transformation,[],[f14])).
% 11.41/1.98  
% 11.41/1.98  fof(f46,plain,(
% 11.41/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(flattening,[],[f45])).
% 11.41/1.98  
% 11.41/1.98  fof(f70,plain,(
% 11.41/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.41/1.98    inference(nnf_transformation,[],[f46])).
% 11.41/1.98  
% 11.41/1.98  fof(f97,plain,(
% 11.41/1.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(cnf_transformation,[],[f70])).
% 11.41/1.98  
% 11.41/1.98  fof(f130,plain,(
% 11.41/1.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.41/1.98    inference(equality_resolution,[],[f97])).
% 11.41/1.98  
% 11.41/1.98  cnf(c_40,negated_conjecture,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
% 11.41/1.98      inference(cnf_transformation,[],[f127]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2590,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_45,negated_conjecture,
% 11.41/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.41/1.98      inference(cnf_transformation,[],[f122]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2585,plain,
% 11.41/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_24,plain,
% 11.41/1.98      ( ~ v3_funct_2(X0,X1,X2)
% 11.41/1.98      | v2_funct_2(X0,X2)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | ~ v1_funct_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f105]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_14,plain,
% 11.41/1.98      ( v5_relat_1(X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.41/1.98      inference(cnf_transformation,[],[f94]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_28,plain,
% 11.41/1.98      ( ~ v2_funct_2(X0,X1)
% 11.41/1.98      | ~ v5_relat_1(X0,X1)
% 11.41/1.98      | ~ v1_relat_1(X0)
% 11.41/1.98      | k2_relat_1(X0) = X1 ),
% 11.41/1.98      inference(cnf_transformation,[],[f106]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_682,plain,
% 11.41/1.98      ( ~ v2_funct_2(X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.41/1.98      | ~ v1_relat_1(X0)
% 11.41/1.98      | k2_relat_1(X0) = X1 ),
% 11.41/1.98      inference(resolution,[status(thm)],[c_14,c_28]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_13,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | v1_relat_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f92]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_694,plain,
% 11.41/1.98      ( ~ v2_funct_2(X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.41/1.98      | k2_relat_1(X0) = X1 ),
% 11.41/1.98      inference(forward_subsumption_resolution,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_682,c_13]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_725,plain,
% 11.41/1.98      ( ~ v3_funct_2(X0,X1,X2)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.41/1.98      | ~ v1_funct_1(X0)
% 11.41/1.98      | X3 != X0
% 11.41/1.98      | X5 != X2
% 11.41/1.98      | k2_relat_1(X3) = X5 ),
% 11.41/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_694]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_726,plain,
% 11.41/1.98      ( ~ v3_funct_2(X0,X1,X2)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.41/1.98      | ~ v1_funct_1(X0)
% 11.41/1.98      | k2_relat_1(X0) = X2 ),
% 11.41/1.98      inference(unflattening,[status(thm)],[c_725]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2579,plain,
% 11.41/1.98      ( k2_relat_1(X0) = X1
% 11.41/1.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 11.41/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6596,plain,
% 11.41/1.98      ( k2_relat_1(sK3) = sK2
% 11.41/1.98      | v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2585,c_2579]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_48,negated_conjecture,
% 11.41/1.98      ( v1_funct_1(sK3) ),
% 11.41/1.98      inference(cnf_transformation,[],[f119]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_46,negated_conjecture,
% 11.41/1.98      ( v3_funct_2(sK3,sK2,sK2) ),
% 11.41/1.98      inference(cnf_transformation,[],[f121]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3101,plain,
% 11.41/1.98      ( ~ v3_funct_2(sK3,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.41/1.98      | ~ v1_funct_1(sK3)
% 11.41/1.98      | k2_relat_1(sK3) = X1 ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_726]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3103,plain,
% 11.41/1.98      ( ~ v3_funct_2(sK3,sK2,sK2)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.41/1.98      | ~ v1_funct_1(sK3)
% 11.41/1.98      | k2_relat_1(sK3) = sK2 ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3101]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7490,plain,
% 11.41/1.98      ( k2_relat_1(sK3) = sK2 ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_6596,c_48,c_46,c_45,c_3103]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_16,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2608,plain,
% 11.41/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.41/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6827,plain,
% 11.41/1.98      ( k2_relset_1(sK2,sK2,sK3) = k2_relat_1(sK3) ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2585,c_2608]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7493,plain,
% 11.41/1.98      ( k2_relset_1(sK2,sK2,sK3) = sK2 ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_7490,c_6827]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_38,plain,
% 11.41/1.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.41/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.41/1.98      | ~ v1_funct_2(X3,X1,X0)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.41/1.98      | ~ v1_funct_1(X2)
% 11.41/1.98      | ~ v1_funct_1(X3)
% 11.41/1.98      | ~ v2_funct_1(X2)
% 11.41/1.98      | k2_relset_1(X0,X1,X2) != X1
% 11.41/1.98      | k2_funct_1(X2) = X3
% 11.41/1.98      | k1_xboole_0 = X1
% 11.41/1.98      | k1_xboole_0 = X0 ),
% 11.41/1.98      inference(cnf_transformation,[],[f118]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2592,plain,
% 11.41/1.98      ( k2_relset_1(X0,X1,X2) != X1
% 11.41/1.98      | k2_funct_1(X2) = X3
% 11.41/1.98      | k1_xboole_0 = X1
% 11.41/1.98      | k1_xboole_0 = X0
% 11.41/1.98      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 11.41/1.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.41/1.98      | v1_funct_2(X3,X1,X0) != iProver_top
% 11.41/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/1.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 11.41/1.98      | v1_funct_1(X2) != iProver_top
% 11.41/1.98      | v1_funct_1(X3) != iProver_top
% 11.41/1.98      | v2_funct_1(X2) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8056,plain,
% 11.41/1.98      ( k2_funct_1(sK3) = X0
% 11.41/1.98      | sK2 = k1_xboole_0
% 11.41/1.98      | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
% 11.41/1.98      | v1_funct_2(X0,sK2,sK2) != iProver_top
% 11.41/1.98      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(X0) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top
% 11.41/1.98      | v2_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_7493,c_2592]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_49,plain,
% 11.41/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_47,negated_conjecture,
% 11.41/1.98      ( v1_funct_2(sK3,sK2,sK2) ),
% 11.41/1.98      inference(cnf_transformation,[],[f120]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_50,plain,
% 11.41/1.98      ( v1_funct_2(sK3,sK2,sK2) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_51,plain,
% 11.41/1.98      ( v3_funct_2(sK3,sK2,sK2) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_52,plain,
% 11.41/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_44,negated_conjecture,
% 11.41/1.98      ( v1_funct_1(sK4) ),
% 11.41/1.98      inference(cnf_transformation,[],[f123]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_53,plain,
% 11.41/1.98      ( v1_funct_1(sK4) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_43,negated_conjecture,
% 11.41/1.98      ( v1_funct_2(sK4,sK2,sK2) ),
% 11.41/1.98      inference(cnf_transformation,[],[f124]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_54,plain,
% 11.41/1.98      ( v1_funct_2(sK4,sK2,sK2) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_41,negated_conjecture,
% 11.41/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.41/1.98      inference(cnf_transformation,[],[f126]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_56,plain,
% 11.41/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_39,negated_conjecture,
% 11.41/1.98      ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
% 11.41/1.98      inference(cnf_transformation,[],[f128]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_58,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_25,plain,
% 11.41/1.98      ( ~ v3_funct_2(X0,X1,X2)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | ~ v1_funct_1(X0)
% 11.41/1.98      | v2_funct_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f104]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3062,plain,
% 11.41/1.98      ( ~ v3_funct_2(sK3,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ v1_funct_1(sK3)
% 11.41/1.98      | v2_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_25]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3063,plain,
% 11.41/1.98      ( v3_funct_2(sK3,X0,X1) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top
% 11.41/1.98      | v2_funct_1(sK3) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_3062]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3065,plain,
% 11.41/1.98      ( v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top
% 11.41/1.98      | v2_funct_1(sK3) = iProver_top ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3063]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_34,plain,
% 11.41/1.98      ( ~ v1_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ v3_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.41/1.98      | ~ v1_funct_1(X0)
% 11.41/1.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 11.41/1.98      inference(cnf_transformation,[],[f110]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3091,plain,
% 11.41/1.98      ( ~ v1_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ v3_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.41/1.98      | v1_funct_1(k2_funct_2(X0,sK3))
% 11.41/1.98      | ~ v1_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_34]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3092,plain,
% 11.41/1.98      ( v1_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.41/1.98      | v1_funct_1(k2_funct_2(X0,sK3)) = iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_3091]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3094,plain,
% 11.41/1.98      ( v1_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(k2_funct_2(sK2,sK3)) = iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3092]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_31,plain,
% 11.41/1.98      ( ~ v1_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ v3_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.41/1.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.41/1.98      | ~ v1_funct_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f113]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3166,plain,
% 11.41/1.98      ( ~ v1_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ v3_funct_2(sK3,X0,X0)
% 11.41/1.98      | m1_subset_1(k2_funct_2(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.41/1.98      | ~ v1_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_31]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3167,plain,
% 11.41/1.98      ( v1_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | m1_subset_1(k2_funct_2(X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_3166]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3169,plain,
% 11.41/1.98      ( v1_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3167]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_33,plain,
% 11.41/1.98      ( ~ v1_funct_2(X0,X1,X1)
% 11.41/1.98      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 11.41/1.98      | ~ v3_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.41/1.98      | ~ v1_funct_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f111]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3186,plain,
% 11.41/1.98      ( v1_funct_2(k2_funct_2(X0,sK3),X0,X0)
% 11.41/1.98      | ~ v1_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ v3_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.41/1.98      | ~ v1_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_33]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3187,plain,
% 11.41/1.98      ( v1_funct_2(k2_funct_2(X0,sK3),X0,X0) = iProver_top
% 11.41/1.98      | v1_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,X0,X0) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3189,plain,
% 11.41/1.98      ( v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2) = iProver_top
% 11.41/1.98      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3187]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_5,plain,
% 11.41/1.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.41/1.98      inference(cnf_transformation,[],[f84]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_37,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,X2,X3)
% 11.41/1.98      | ~ v1_funct_2(X3,X0,X1)
% 11.41/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | r2_hidden(sK1(X0,X2,X3),X0)
% 11.41/1.98      | ~ v1_funct_1(X2)
% 11.41/1.98      | ~ v1_funct_1(X3) ),
% 11.41/1.98      inference(cnf_transformation,[],[f116]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_770,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,X2,X3)
% 11.41/1.98      | ~ v1_funct_2(X3,X0,X1)
% 11.41/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ v1_funct_1(X3)
% 11.41/1.98      | ~ v1_funct_1(X2)
% 11.41/1.98      | ~ v1_xboole_0(X4)
% 11.41/1.98      | X0 != X4
% 11.41/1.98      | sK1(X0,X2,X3) != X5 ),
% 11.41/1.98      inference(resolution_lifted,[status(thm)],[c_5,c_37]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_771,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,X2,X3)
% 11.41/1.98      | ~ v1_funct_2(X3,X0,X1)
% 11.41/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ v1_funct_1(X2)
% 11.41/1.98      | ~ v1_funct_1(X3)
% 11.41/1.98      | ~ v1_xboole_0(X0) ),
% 11.41/1.98      inference(unflattening,[status(thm)],[c_770]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3225,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,sK4,X2)
% 11.41/1.98      | ~ v1_funct_2(X2,X0,X1)
% 11.41/1.98      | ~ v1_funct_2(sK4,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ v1_funct_1(X2)
% 11.41/1.98      | ~ v1_funct_1(sK4)
% 11.41/1.98      | ~ v1_xboole_0(X0) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_771]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_4479,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,sK4,k2_funct_2(X2,sK3))
% 11.41/1.98      | ~ v1_funct_2(k2_funct_2(X2,sK3),X0,X1)
% 11.41/1.98      | ~ v1_funct_2(sK4,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(k2_funct_2(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ v1_funct_1(k2_funct_2(X2,sK3))
% 11.41/1.98      | ~ v1_funct_1(sK4)
% 11.41/1.98      | ~ v1_xboole_0(X0) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3225]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_4480,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,sK4,k2_funct_2(X2,sK3)) = iProver_top
% 11.41/1.98      | v1_funct_2(k2_funct_2(X2,sK3),X0,X1) != iProver_top
% 11.41/1.98      | v1_funct_2(sK4,X0,X1) != iProver_top
% 11.41/1.98      | m1_subset_1(k2_funct_2(X2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/1.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.41/1.98      | v1_funct_1(k2_funct_2(X2,sK3)) != iProver_top
% 11.41/1.98      | v1_funct_1(sK4) != iProver_top
% 11.41/1.98      | v1_xboole_0(X0) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_4479]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_4482,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) = iProver_top
% 11.41/1.98      | v1_funct_2(k2_funct_2(sK2,sK3),sK2,sK2) != iProver_top
% 11.41/1.98      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(k2_funct_2(sK2,sK3)) != iProver_top
% 11.41/1.98      | v1_funct_1(sK4) != iProver_top
% 11.41/1.98      | v1_xboole_0(sK2) != iProver_top ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_4480]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2589,plain,
% 11.41/1.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6595,plain,
% 11.41/1.98      ( k2_relat_1(sK4) = sK2
% 11.41/1.98      | v3_funct_2(sK4,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2589,c_2579]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_42,negated_conjecture,
% 11.41/1.98      ( v3_funct_2(sK4,sK2,sK2) ),
% 11.41/1.98      inference(cnf_transformation,[],[f125]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3096,plain,
% 11.41/1.98      ( ~ v3_funct_2(sK4,X0,X1)
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.41/1.98      | ~ v1_funct_1(sK4)
% 11.41/1.98      | k2_relat_1(sK4) = X1 ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_726]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3098,plain,
% 11.41/1.98      ( ~ v3_funct_2(sK4,sK2,sK2)
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.41/1.98      | ~ v1_funct_1(sK4)
% 11.41/1.98      | k2_relat_1(sK4) = sK2 ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3096]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7480,plain,
% 11.41/1.98      ( k2_relat_1(sK4) = sK2 ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_6595,c_44,c_42,c_41,c_3098]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2609,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_5242,plain,
% 11.41/1.98      ( v1_relat_1(sK4) = iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2589,c_2609]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_9,plain,
% 11.41/1.98      ( ~ v1_relat_1(X0)
% 11.41/1.98      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f88]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2613,plain,
% 11.41/1.98      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 11.41/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_5866,plain,
% 11.41/1.98      ( k2_xboole_0(k1_relat_1(sK4),k2_relat_1(sK4)) = k3_relat_1(sK4) ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_5242,c_2613]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7484,plain,
% 11.41/1.98      ( k2_xboole_0(k1_relat_1(sK4),sK2) = k3_relat_1(sK4) ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_7480,c_5866]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_15,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | v4_relat_1(X0,X1) ),
% 11.41/1.98      inference(cnf_transformation,[],[f93]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8,plain,
% 11.41/1.98      ( ~ v4_relat_1(X0,X1)
% 11.41/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.98      | ~ v1_relat_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f86]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_661,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.98      | ~ v1_relat_1(X0) ),
% 11.41/1.98      inference(resolution,[status(thm)],[c_15,c_8]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_665,plain,
% 11.41/1.98      ( r1_tarski(k1_relat_1(X0),X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_661,c_13]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_666,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.41/1.98      inference(renaming,[status(thm)],[c_665]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2580,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6575,plain,
% 11.41/1.98      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2589,c_2580]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_1,plain,
% 11.41/1.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.41/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2616,plain,
% 11.41/1.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7078,plain,
% 11.41/1.98      ( k2_xboole_0(k1_relat_1(sK4),sK2) = sK2 ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_6575,c_2616]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8060,plain,
% 11.41/1.98      ( k3_relat_1(sK4) = sK2 ),
% 11.41/1.98      inference(light_normalisation,[status(thm)],[c_7484,c_7078]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_20,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.41/1.98      | r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2)) ),
% 11.41/1.98      inference(cnf_transformation,[],[f99]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2604,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.41/1.98      | r1_tarski(k3_relat_1(X0),k2_xboole_0(X1,X2)) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7669,plain,
% 11.41/1.98      ( r1_tarski(k3_relat_1(sK4),k2_xboole_0(sK2,sK2)) = iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2589,c_2604]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_0,plain,
% 11.41/1.98      ( k2_xboole_0(X0,X0) = X0 ),
% 11.41/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_7675,plain,
% 11.41/1.98      ( r1_tarski(k3_relat_1(sK4),sK2) = iProver_top ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_7669,c_0]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8062,plain,
% 11.41/1.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_8060,c_7675]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2,plain,
% 11.41/1.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.41/1.98      inference(cnf_transformation,[],[f82]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2615,plain,
% 11.41/1.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8070,plain,
% 11.41/1.98      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_8062,c_2615]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6,plain,
% 11.41/1.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 11.41/1.98      inference(cnf_transformation,[],[f85]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_4,plain,
% 11.41/1.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_625,plain,
% 11.41/1.98      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | k4_xboole_0(X0,X1) != X0 ),
% 11.41/1.98      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2581,plain,
% 11.41/1.98      ( k4_xboole_0(X0,X1) != X0
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.41/1.98      | v1_xboole_0(X0) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_26079,plain,
% 11.41/1.98      ( sK2 != k1_xboole_0
% 11.41/1.98      | r1_tarski(sK2,sK2) != iProver_top
% 11.41/1.98      | v1_xboole_0(sK2) = iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_8070,c_2581]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_31702,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | k2_funct_1(sK3) = X0
% 11.41/1.98      | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
% 11.41/1.98      | v1_funct_2(X0,sK2,sK2) != iProver_top
% 11.41/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_8056,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_58,c_3065,
% 11.41/1.98                 c_3094,c_3169,c_3189,c_4482,c_8062,c_26079]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_31703,plain,
% 11.41/1.98      ( k2_funct_1(sK3) = X0
% 11.41/1.98      | r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X0),k6_partfun1(sK2)) != iProver_top
% 11.41/1.98      | v1_funct_2(X0,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.41/1.98      inference(renaming,[status(thm)],[c_31702]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_31713,plain,
% 11.41/1.98      ( k2_funct_1(sK3) = sK4
% 11.41/1.98      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 11.41/1.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 11.41/1.98      | v1_funct_1(sK4) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2590,c_31703]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_32136,plain,
% 11.41/1.98      ( k2_funct_1(sK3) = sK4 ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_31713,c_53,c_54,c_56]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_35,plain,
% 11.41/1.98      ( ~ v1_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ v3_funct_2(X0,X1,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.41/1.98      | ~ v1_funct_1(X0)
% 11.41/1.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f114]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2594,plain,
% 11.41/1.98      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 11.41/1.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 11.41/1.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 11.41/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.41/1.98      | v1_funct_1(X1) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_9525,plain,
% 11.41/1.98      ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3)
% 11.41/1.98      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | v3_funct_2(sK3,sK2,sK2) != iProver_top
% 11.41/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_2585,c_2594]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3131,plain,
% 11.41/1.98      ( ~ v1_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ v3_funct_2(sK3,X0,X0)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 11.41/1.98      | ~ v1_funct_1(sK3)
% 11.41/1.98      | k2_funct_2(X0,sK3) = k2_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_35]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3133,plain,
% 11.41/1.98      ( ~ v1_funct_2(sK3,sK2,sK2)
% 11.41/1.98      | ~ v3_funct_2(sK3,sK2,sK2)
% 11.41/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 11.41/1.98      | ~ v1_funct_1(sK3)
% 11.41/1.98      | k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_3131]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_10939,plain,
% 11.41/1.98      ( k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
% 11.41/1.98      inference(global_propositional_subsumption,
% 11.41/1.98                [status(thm)],
% 11.41/1.98                [c_9525,c_48,c_47,c_46,c_45,c_3133]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_2591,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_10942,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3)) != iProver_top ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_10939,c_2591]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_32170,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,sK4) != iProver_top ),
% 11.41/1.98      inference(demodulation,[status(thm)],[c_32136,c_10942]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_17,plain,
% 11.41/1.98      ( r2_relset_1(X0,X1,X2,X2)
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.41/1.98      inference(cnf_transformation,[],[f130]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3051,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,sK4)
% 11.41/1.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 11.41/1.98      inference(instantiation,[status(thm)],[c_17]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3052,plain,
% 11.41/1.98      ( r2_relset_1(sK2,sK2,sK4,sK4) = iProver_top
% 11.41/1.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_3051]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(contradiction,plain,
% 11.41/1.98      ( $false ),
% 11.41/1.98      inference(minisat,[status(thm)],[c_32170,c_3052,c_56]) ).
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  ------                               Statistics
% 11.41/1.98  
% 11.41/1.98  ------ General
% 11.41/1.98  
% 11.41/1.98  abstr_ref_over_cycles:                  0
% 11.41/1.98  abstr_ref_under_cycles:                 0
% 11.41/1.98  gc_basic_clause_elim:                   0
% 11.41/1.98  forced_gc_time:                         0
% 11.41/1.98  parsing_time:                           0.011
% 11.41/1.98  unif_index_cands_time:                  0.
% 11.41/1.98  unif_index_add_time:                    0.
% 11.41/1.98  orderings_time:                         0.
% 11.41/1.98  out_proof_time:                         0.016
% 11.41/1.98  total_time:                             1.183
% 11.41/1.98  num_of_symbols:                         66
% 11.41/1.98  num_of_terms:                           60840
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing
% 11.41/1.98  
% 11.41/1.98  num_of_splits:                          0
% 11.41/1.98  num_of_split_atoms:                     0
% 11.41/1.98  num_of_reused_defs:                     0
% 11.41/1.98  num_eq_ax_congr_red:                    67
% 11.41/1.98  num_of_sem_filtered_clauses:            1
% 11.41/1.98  num_of_subtypes:                        0
% 11.41/1.98  monotx_restored_types:                  0
% 11.41/1.98  sat_num_of_epr_types:                   0
% 11.41/1.98  sat_num_of_non_cyclic_types:            0
% 11.41/1.98  sat_guarded_non_collapsed_types:        0
% 11.41/1.98  num_pure_diseq_elim:                    0
% 11.41/1.98  simp_replaced_by:                       0
% 11.41/1.98  res_preprocessed:                       206
% 11.41/1.98  prep_upred:                             0
% 11.41/1.98  prep_unflattend:                        37
% 11.41/1.98  smt_new_axioms:                         0
% 11.41/1.98  pred_elim_cands:                        9
% 11.41/1.98  pred_elim:                              5
% 11.41/1.98  pred_elim_cl:                           7
% 11.41/1.98  pred_elim_cycles:                       12
% 11.41/1.98  merged_defs:                            8
% 11.41/1.98  merged_defs_ncl:                        0
% 11.41/1.98  bin_hyper_res:                          8
% 11.41/1.98  prep_cycles:                            4
% 11.41/1.98  pred_elim_time:                         0.016
% 11.41/1.98  splitting_time:                         0.
% 11.41/1.98  sem_filter_time:                        0.
% 11.41/1.98  monotx_time:                            0.001
% 11.41/1.98  subtype_inf_time:                       0.
% 11.41/1.98  
% 11.41/1.98  ------ Problem properties
% 11.41/1.98  
% 11.41/1.98  clauses:                                41
% 11.41/1.98  conjectures:                            10
% 11.41/1.98  epr:                                    6
% 11.41/1.98  horn:                                   40
% 11.41/1.98  ground:                                 10
% 11.41/1.98  unary:                                  12
% 11.41/1.98  binary:                                 9
% 11.41/1.98  lits:                                   131
% 11.41/1.98  lits_eq:                                17
% 11.41/1.98  fd_pure:                                0
% 11.41/1.98  fd_pseudo:                              0
% 11.41/1.98  fd_cond:                                0
% 11.41/1.98  fd_pseudo_cond:                         3
% 11.41/1.98  ac_symbols:                             0
% 11.41/1.98  
% 11.41/1.98  ------ Propositional Solver
% 11.41/1.98  
% 11.41/1.98  prop_solver_calls:                      31
% 11.41/1.98  prop_fast_solver_calls:                 2063
% 11.41/1.98  smt_solver_calls:                       0
% 11.41/1.98  smt_fast_solver_calls:                  0
% 11.41/1.98  prop_num_of_clauses:                    14843
% 11.41/1.98  prop_preprocess_simplified:             28951
% 11.41/1.98  prop_fo_subsumed:                       114
% 11.41/1.98  prop_solver_time:                       0.
% 11.41/1.98  smt_solver_time:                        0.
% 11.41/1.98  smt_fast_solver_time:                   0.
% 11.41/1.98  prop_fast_solver_time:                  0.
% 11.41/1.98  prop_unsat_core_time:                   0.002
% 11.41/1.98  
% 11.41/1.98  ------ QBF
% 11.41/1.98  
% 11.41/1.98  qbf_q_res:                              0
% 11.41/1.98  qbf_num_tautologies:                    0
% 11.41/1.98  qbf_prep_cycles:                        0
% 11.41/1.98  
% 11.41/1.98  ------ BMC1
% 11.41/1.98  
% 11.41/1.98  bmc1_current_bound:                     -1
% 11.41/1.99  bmc1_last_solved_bound:                 -1
% 11.41/1.99  bmc1_unsat_core_size:                   -1
% 11.41/1.99  bmc1_unsat_core_parents_size:           -1
% 11.41/1.99  bmc1_merge_next_fun:                    0
% 11.41/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.41/1.99  
% 11.41/1.99  ------ Instantiation
% 11.41/1.99  
% 11.41/1.99  inst_num_of_clauses:                    3947
% 11.41/1.99  inst_num_in_passive:                    1271
% 11.41/1.99  inst_num_in_active:                     789
% 11.41/1.99  inst_num_in_unprocessed:                1887
% 11.41/1.99  inst_num_of_loops:                      950
% 11.41/1.99  inst_num_of_learning_restarts:          0
% 11.41/1.99  inst_num_moves_active_passive:          161
% 11.41/1.99  inst_lit_activity:                      0
% 11.41/1.99  inst_lit_activity_moves:                4
% 11.41/1.99  inst_num_tautologies:                   0
% 11.41/1.99  inst_num_prop_implied:                  0
% 11.41/1.99  inst_num_existing_simplified:           0
% 11.41/1.99  inst_num_eq_res_simplified:             0
% 11.41/1.99  inst_num_child_elim:                    0
% 11.41/1.99  inst_num_of_dismatching_blockings:      1072
% 11.41/1.99  inst_num_of_non_proper_insts:           3004
% 11.41/1.99  inst_num_of_duplicates:                 0
% 11.41/1.99  inst_inst_num_from_inst_to_res:         0
% 11.41/1.99  inst_dismatching_checking_time:         0.
% 11.41/1.99  
% 11.41/1.99  ------ Resolution
% 11.41/1.99  
% 11.41/1.99  res_num_of_clauses:                     0
% 11.41/1.99  res_num_in_passive:                     0
% 11.41/1.99  res_num_in_active:                      0
% 11.41/1.99  res_num_of_loops:                       210
% 11.41/1.99  res_forward_subset_subsumed:            51
% 11.41/1.99  res_backward_subset_subsumed:           0
% 11.41/1.99  res_forward_subsumed:                   0
% 11.41/1.99  res_backward_subsumed:                  0
% 11.41/1.99  res_forward_subsumption_resolution:     2
% 11.41/1.99  res_backward_subsumption_resolution:    0
% 11.41/1.99  res_clause_to_clause_subsumption:       892
% 11.41/1.99  res_orphan_elimination:                 0
% 11.41/1.99  res_tautology_del:                      61
% 11.41/1.99  res_num_eq_res_simplified:              0
% 11.41/1.99  res_num_sel_changes:                    0
% 11.41/1.99  res_moves_from_active_to_pass:          0
% 11.41/1.99  
% 11.41/1.99  ------ Superposition
% 11.41/1.99  
% 11.41/1.99  sup_time_total:                         0.
% 11.41/1.99  sup_time_generating:                    0.
% 11.41/1.99  sup_time_sim_full:                      0.
% 11.41/1.99  sup_time_sim_immed:                     0.
% 11.41/1.99  
% 11.41/1.99  sup_num_of_clauses:                     229
% 11.41/1.99  sup_num_in_active:                      142
% 11.41/1.99  sup_num_in_passive:                     87
% 11.41/1.99  sup_num_of_loops:                       188
% 11.41/1.99  sup_fw_superposition:                   148
% 11.41/1.99  sup_bw_superposition:                   136
% 11.41/1.99  sup_immediate_simplified:               46
% 11.41/1.99  sup_given_eliminated:                   0
% 11.41/1.99  comparisons_done:                       0
% 11.41/1.99  comparisons_avoided:                    0
% 11.41/1.99  
% 11.41/1.99  ------ Simplifications
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  sim_fw_subset_subsumed:                 26
% 11.41/1.99  sim_bw_subset_subsumed:                 1
% 11.41/1.99  sim_fw_subsumed:                        10
% 11.41/1.99  sim_bw_subsumed:                        0
% 11.41/1.99  sim_fw_subsumption_res:                 0
% 11.41/1.99  sim_bw_subsumption_res:                 0
% 11.41/1.99  sim_tautology_del:                      5
% 11.41/1.99  sim_eq_tautology_del:                   7
% 11.41/1.99  sim_eq_res_simp:                        0
% 11.41/1.99  sim_fw_demodulated:                     8
% 11.41/1.99  sim_bw_demodulated:                     45
% 11.41/1.99  sim_light_normalised:                   20
% 11.41/1.99  sim_joinable_taut:                      0
% 11.41/1.99  sim_joinable_simp:                      0
% 11.41/1.99  sim_ac_normalised:                      0
% 11.41/1.99  sim_smt_subsumption:                    0
% 11.41/1.99  
%------------------------------------------------------------------------------
