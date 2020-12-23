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
% DateTime   : Thu Dec  3 12:07:13 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 516 expanded)
%              Number of clauses        :  100 ( 182 expanded)
%              Number of leaves         :   21 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  667 (3407 expanded)
%              Number of equality atoms :  224 ( 349 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f55,f54])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2445,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2452,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6560,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2452])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2450,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_22,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_537,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_538,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_554,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_538,c_13])).

cnf(c_2438,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_3979,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2438])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_101,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3278,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_2462])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_293,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_368,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_294])).

cnf(c_2439,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_3819,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3278,c_2439])).

cnf(c_4790,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3979,c_41,c_43,c_103,c_3819])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2459,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4253,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2445,c_2459])).

cnf(c_4792,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4790,c_4253])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f87])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_215,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_29])).

cnf(c_216,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_2441,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_5076,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4792,c_2441])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_42,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_120,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1671,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2891,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_2892,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2891])).

cnf(c_2894,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2892])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2449,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5142,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_2460])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1668,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1697,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2535,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1676,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X5 != X1
    | X4 != X0
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2511,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) != X3
    | sK3 != X2
    | sK1 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_2700,plain,
    ( ~ r2_relset_1(X0,X1,sK3,X2)
    | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) != X2
    | sK3 != sK3
    | sK1 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_2702,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | ~ r2_relset_1(sK1,sK1,sK3,sK1)
    | k2_funct_2(sK1,sK2) != sK1
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_2708,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2871,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2872,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2871])).

cnf(c_2874,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2872])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2924,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2925,plain,
    ( X0 = sK3
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_2927,plain,
    ( sK1 = sK3
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_2977,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2978,plain,
    ( k2_funct_2(sK1,sK2) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2977])).

cnf(c_2980,plain,
    ( k2_funct_2(sK1,sK2) = sK1
    | v1_xboole_0(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_2637,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | X2 != sK3
    | X3 != sK3
    | X0 != sK1
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_3003,plain,
    ( r2_relset_1(X0,X1,sK3,X2)
    | ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | X2 != sK3
    | X0 != sK1
    | X1 != sK1
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_3010,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | r2_relset_1(sK1,sK1,sK3,sK1)
    | sK3 != sK3
    | sK1 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_4047,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4048,plain,
    ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4047])).

cnf(c_4050,plain,
    ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4048])).

cnf(c_4052,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4053,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4052])).

cnf(c_4055,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4053])).

cnf(c_5206,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5142,c_41,c_42,c_43,c_44,c_33,c_48,c_31,c_1697,c_2535,c_2702,c_2708,c_2874,c_2927,c_2980,c_3010,c_4050,c_4055])).

cnf(c_5275,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5076,c_41,c_42,c_43,c_44,c_33,c_48,c_31,c_120,c_1697,c_2535,c_2702,c_2708,c_2874,c_2894,c_2927,c_2980,c_3010,c_4050,c_4055])).

cnf(c_5276,plain,
    ( k2_funct_1(sK2) = X0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5275])).

cnf(c_5281,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_5276])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5410,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5281,c_45,c_46,c_48])).

cnf(c_6563,plain,
    ( k2_funct_2(sK1,sK2) = sK3
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6560,c_5410])).

cnf(c_2563,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | k2_funct_2(sK1,sK2) != sK3
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6563,c_2708,c_2563,c_2535,c_1697,c_31,c_33,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.40/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.96  
% 3.40/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.96  
% 3.40/0.96  ------  iProver source info
% 3.40/0.96  
% 3.40/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.96  git: non_committed_changes: false
% 3.40/0.96  git: last_make_outside_of_git: false
% 3.40/0.96  
% 3.40/0.96  ------ 
% 3.40/0.96  
% 3.40/0.96  ------ Input Options
% 3.40/0.96  
% 3.40/0.96  --out_options                           all
% 3.40/0.96  --tptp_safe_out                         true
% 3.40/0.96  --problem_path                          ""
% 3.40/0.96  --include_path                          ""
% 3.40/0.96  --clausifier                            res/vclausify_rel
% 3.40/0.96  --clausifier_options                    ""
% 3.40/0.96  --stdin                                 false
% 3.40/0.96  --stats_out                             all
% 3.40/0.96  
% 3.40/0.96  ------ General Options
% 3.40/0.96  
% 3.40/0.96  --fof                                   false
% 3.40/0.96  --time_out_real                         305.
% 3.40/0.96  --time_out_virtual                      -1.
% 3.40/0.96  --symbol_type_check                     false
% 3.40/0.96  --clausify_out                          false
% 3.40/0.96  --sig_cnt_out                           false
% 3.40/0.96  --trig_cnt_out                          false
% 3.40/0.96  --trig_cnt_out_tolerance                1.
% 3.40/0.96  --trig_cnt_out_sk_spl                   false
% 3.40/0.96  --abstr_cl_out                          false
% 3.40/0.96  
% 3.40/0.96  ------ Global Options
% 3.40/0.96  
% 3.40/0.96  --schedule                              default
% 3.40/0.96  --add_important_lit                     false
% 3.40/0.96  --prop_solver_per_cl                    1000
% 3.40/0.96  --min_unsat_core                        false
% 3.40/0.96  --soft_assumptions                      false
% 3.40/0.96  --soft_lemma_size                       3
% 3.40/0.96  --prop_impl_unit_size                   0
% 3.40/0.96  --prop_impl_unit                        []
% 3.40/0.96  --share_sel_clauses                     true
% 3.40/0.96  --reset_solvers                         false
% 3.40/0.96  --bc_imp_inh                            [conj_cone]
% 3.40/0.96  --conj_cone_tolerance                   3.
% 3.40/0.96  --extra_neg_conj                        none
% 3.40/0.96  --large_theory_mode                     true
% 3.40/0.96  --prolific_symb_bound                   200
% 3.40/0.96  --lt_threshold                          2000
% 3.40/0.96  --clause_weak_htbl                      true
% 3.40/0.96  --gc_record_bc_elim                     false
% 3.40/0.96  
% 3.40/0.96  ------ Preprocessing Options
% 3.40/0.96  
% 3.40/0.96  --preprocessing_flag                    true
% 3.40/0.96  --time_out_prep_mult                    0.1
% 3.40/0.96  --splitting_mode                        input
% 3.40/0.96  --splitting_grd                         true
% 3.40/0.96  --splitting_cvd                         false
% 3.40/0.96  --splitting_cvd_svl                     false
% 3.40/0.96  --splitting_nvd                         32
% 3.40/0.96  --sub_typing                            true
% 3.40/0.96  --prep_gs_sim                           true
% 3.40/0.96  --prep_unflatten                        true
% 3.40/0.96  --prep_res_sim                          true
% 3.40/0.96  --prep_upred                            true
% 3.40/0.96  --prep_sem_filter                       exhaustive
% 3.40/0.96  --prep_sem_filter_out                   false
% 3.40/0.96  --pred_elim                             true
% 3.40/0.96  --res_sim_input                         true
% 3.40/0.96  --eq_ax_congr_red                       true
% 3.40/0.96  --pure_diseq_elim                       true
% 3.40/0.96  --brand_transform                       false
% 3.40/0.96  --non_eq_to_eq                          false
% 3.40/0.96  --prep_def_merge                        true
% 3.40/0.96  --prep_def_merge_prop_impl              false
% 3.40/0.96  --prep_def_merge_mbd                    true
% 3.40/0.96  --prep_def_merge_tr_red                 false
% 3.40/0.96  --prep_def_merge_tr_cl                  false
% 3.40/0.96  --smt_preprocessing                     true
% 3.40/0.96  --smt_ac_axioms                         fast
% 3.40/0.96  --preprocessed_out                      false
% 3.40/0.96  --preprocessed_stats                    false
% 3.40/0.96  
% 3.40/0.96  ------ Abstraction refinement Options
% 3.40/0.96  
% 3.40/0.96  --abstr_ref                             []
% 3.40/0.96  --abstr_ref_prep                        false
% 3.40/0.96  --abstr_ref_until_sat                   false
% 3.40/0.96  --abstr_ref_sig_restrict                funpre
% 3.40/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.96  --abstr_ref_under                       []
% 3.40/0.96  
% 3.40/0.96  ------ SAT Options
% 3.40/0.96  
% 3.40/0.96  --sat_mode                              false
% 3.40/0.96  --sat_fm_restart_options                ""
% 3.40/0.96  --sat_gr_def                            false
% 3.40/0.96  --sat_epr_types                         true
% 3.40/0.96  --sat_non_cyclic_types                  false
% 3.40/0.96  --sat_finite_models                     false
% 3.40/0.96  --sat_fm_lemmas                         false
% 3.40/0.96  --sat_fm_prep                           false
% 3.40/0.96  --sat_fm_uc_incr                        true
% 3.40/0.96  --sat_out_model                         small
% 3.40/0.96  --sat_out_clauses                       false
% 3.40/0.96  
% 3.40/0.96  ------ QBF Options
% 3.40/0.96  
% 3.40/0.96  --qbf_mode                              false
% 3.40/0.96  --qbf_elim_univ                         false
% 3.40/0.96  --qbf_dom_inst                          none
% 3.40/0.96  --qbf_dom_pre_inst                      false
% 3.40/0.96  --qbf_sk_in                             false
% 3.40/0.96  --qbf_pred_elim                         true
% 3.40/0.96  --qbf_split                             512
% 3.40/0.96  
% 3.40/0.96  ------ BMC1 Options
% 3.40/0.96  
% 3.40/0.96  --bmc1_incremental                      false
% 3.40/0.96  --bmc1_axioms                           reachable_all
% 3.40/0.96  --bmc1_min_bound                        0
% 3.40/0.96  --bmc1_max_bound                        -1
% 3.40/0.96  --bmc1_max_bound_default                -1
% 3.40/0.96  --bmc1_symbol_reachability              true
% 3.40/0.96  --bmc1_property_lemmas                  false
% 3.40/0.96  --bmc1_k_induction                      false
% 3.40/0.96  --bmc1_non_equiv_states                 false
% 3.40/0.96  --bmc1_deadlock                         false
% 3.40/0.96  --bmc1_ucm                              false
% 3.40/0.96  --bmc1_add_unsat_core                   none
% 3.40/0.96  --bmc1_unsat_core_children              false
% 3.40/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.96  --bmc1_out_stat                         full
% 3.40/0.96  --bmc1_ground_init                      false
% 3.40/0.96  --bmc1_pre_inst_next_state              false
% 3.40/0.96  --bmc1_pre_inst_state                   false
% 3.40/0.96  --bmc1_pre_inst_reach_state             false
% 3.40/0.96  --bmc1_out_unsat_core                   false
% 3.40/0.96  --bmc1_aig_witness_out                  false
% 3.40/0.96  --bmc1_verbose                          false
% 3.40/0.96  --bmc1_dump_clauses_tptp                false
% 3.40/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.96  --bmc1_dump_file                        -
% 3.40/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.96  --bmc1_ucm_extend_mode                  1
% 3.40/0.96  --bmc1_ucm_init_mode                    2
% 3.40/0.96  --bmc1_ucm_cone_mode                    none
% 3.40/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.96  --bmc1_ucm_relax_model                  4
% 3.40/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.96  --bmc1_ucm_layered_model                none
% 3.40/0.96  --bmc1_ucm_max_lemma_size               10
% 3.40/0.96  
% 3.40/0.96  ------ AIG Options
% 3.40/0.96  
% 3.40/0.96  --aig_mode                              false
% 3.40/0.96  
% 3.40/0.96  ------ Instantiation Options
% 3.40/0.96  
% 3.40/0.96  --instantiation_flag                    true
% 3.40/0.96  --inst_sos_flag                         true
% 3.40/0.96  --inst_sos_phase                        true
% 3.40/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.96  --inst_lit_sel_side                     num_symb
% 3.40/0.96  --inst_solver_per_active                1400
% 3.40/0.96  --inst_solver_calls_frac                1.
% 3.40/0.96  --inst_passive_queue_type               priority_queues
% 3.40/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.96  --inst_passive_queues_freq              [25;2]
% 3.40/0.96  --inst_dismatching                      true
% 3.40/0.96  --inst_eager_unprocessed_to_passive     true
% 3.40/0.96  --inst_prop_sim_given                   true
% 3.40/0.96  --inst_prop_sim_new                     false
% 3.40/0.96  --inst_subs_new                         false
% 3.40/0.96  --inst_eq_res_simp                      false
% 3.40/0.96  --inst_subs_given                       false
% 3.40/0.96  --inst_orphan_elimination               true
% 3.40/0.96  --inst_learning_loop_flag               true
% 3.40/0.96  --inst_learning_start                   3000
% 3.40/0.96  --inst_learning_factor                  2
% 3.40/0.96  --inst_start_prop_sim_after_learn       3
% 3.40/0.96  --inst_sel_renew                        solver
% 3.40/0.96  --inst_lit_activity_flag                true
% 3.40/0.96  --inst_restr_to_given                   false
% 3.40/0.96  --inst_activity_threshold               500
% 3.40/0.96  --inst_out_proof                        true
% 3.40/0.96  
% 3.40/0.96  ------ Resolution Options
% 3.40/0.96  
% 3.40/0.96  --resolution_flag                       true
% 3.40/0.96  --res_lit_sel                           adaptive
% 3.40/0.96  --res_lit_sel_side                      none
% 3.40/0.96  --res_ordering                          kbo
% 3.40/0.96  --res_to_prop_solver                    active
% 3.40/0.96  --res_prop_simpl_new                    false
% 3.40/0.96  --res_prop_simpl_given                  true
% 3.40/0.96  --res_passive_queue_type                priority_queues
% 3.40/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.96  --res_passive_queues_freq               [15;5]
% 3.40/0.96  --res_forward_subs                      full
% 3.40/0.96  --res_backward_subs                     full
% 3.40/0.96  --res_forward_subs_resolution           true
% 3.40/0.96  --res_backward_subs_resolution          true
% 3.40/0.96  --res_orphan_elimination                true
% 3.40/0.96  --res_time_limit                        2.
% 3.40/0.96  --res_out_proof                         true
% 3.40/0.96  
% 3.40/0.96  ------ Superposition Options
% 3.40/0.96  
% 3.40/0.96  --superposition_flag                    true
% 3.40/0.96  --sup_passive_queue_type                priority_queues
% 3.40/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.96  --demod_completeness_check              fast
% 3.40/0.96  --demod_use_ground                      true
% 3.40/0.96  --sup_to_prop_solver                    passive
% 3.40/0.96  --sup_prop_simpl_new                    true
% 3.40/0.96  --sup_prop_simpl_given                  true
% 3.40/0.96  --sup_fun_splitting                     true
% 3.40/0.96  --sup_smt_interval                      50000
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Simplification Setup
% 3.40/0.97  
% 3.40/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/0.97  --sup_immed_triv                        [TrivRules]
% 3.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_bw_main                     []
% 3.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_input_bw                          []
% 3.40/0.97  
% 3.40/0.97  ------ Combination Options
% 3.40/0.97  
% 3.40/0.97  --comb_res_mult                         3
% 3.40/0.97  --comb_sup_mult                         2
% 3.40/0.97  --comb_inst_mult                        10
% 3.40/0.97  
% 3.40/0.97  ------ Debug Options
% 3.40/0.97  
% 3.40/0.97  --dbg_backtrace                         false
% 3.40/0.97  --dbg_dump_prop_clauses                 false
% 3.40/0.97  --dbg_dump_prop_clauses_file            -
% 3.40/0.97  --dbg_out_stat                          false
% 3.40/0.97  ------ Parsing...
% 3.40/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.97  ------ Proving...
% 3.40/0.97  ------ Problem Properties 
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  clauses                                 35
% 3.40/0.97  conjectures                             10
% 3.40/0.97  EPR                                     11
% 3.40/0.97  Horn                                    32
% 3.40/0.97  unary                                   14
% 3.40/0.97  binary                                  6
% 3.40/0.97  lits                                    98
% 3.40/0.97  lits eq                                 15
% 3.40/0.97  fd_pure                                 0
% 3.40/0.97  fd_pseudo                               0
% 3.40/0.97  fd_cond                                 1
% 3.40/0.97  fd_pseudo_cond                          5
% 3.40/0.97  AC symbols                              0
% 3.40/0.97  
% 3.40/0.97  ------ Schedule dynamic 5 is on 
% 3.40/0.97  
% 3.40/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  ------ 
% 3.40/0.97  Current options:
% 3.40/0.97  ------ 
% 3.40/0.97  
% 3.40/0.97  ------ Input Options
% 3.40/0.97  
% 3.40/0.97  --out_options                           all
% 3.40/0.97  --tptp_safe_out                         true
% 3.40/0.97  --problem_path                          ""
% 3.40/0.97  --include_path                          ""
% 3.40/0.97  --clausifier                            res/vclausify_rel
% 3.40/0.97  --clausifier_options                    ""
% 3.40/0.97  --stdin                                 false
% 3.40/0.97  --stats_out                             all
% 3.40/0.97  
% 3.40/0.97  ------ General Options
% 3.40/0.97  
% 3.40/0.97  --fof                                   false
% 3.40/0.97  --time_out_real                         305.
% 3.40/0.97  --time_out_virtual                      -1.
% 3.40/0.97  --symbol_type_check                     false
% 3.40/0.97  --clausify_out                          false
% 3.40/0.97  --sig_cnt_out                           false
% 3.40/0.97  --trig_cnt_out                          false
% 3.40/0.97  --trig_cnt_out_tolerance                1.
% 3.40/0.97  --trig_cnt_out_sk_spl                   false
% 3.40/0.97  --abstr_cl_out                          false
% 3.40/0.97  
% 3.40/0.97  ------ Global Options
% 3.40/0.97  
% 3.40/0.97  --schedule                              default
% 3.40/0.97  --add_important_lit                     false
% 3.40/0.97  --prop_solver_per_cl                    1000
% 3.40/0.97  --min_unsat_core                        false
% 3.40/0.97  --soft_assumptions                      false
% 3.40/0.97  --soft_lemma_size                       3
% 3.40/0.97  --prop_impl_unit_size                   0
% 3.40/0.97  --prop_impl_unit                        []
% 3.40/0.97  --share_sel_clauses                     true
% 3.40/0.97  --reset_solvers                         false
% 3.40/0.97  --bc_imp_inh                            [conj_cone]
% 3.40/0.97  --conj_cone_tolerance                   3.
% 3.40/0.97  --extra_neg_conj                        none
% 3.40/0.97  --large_theory_mode                     true
% 3.40/0.97  --prolific_symb_bound                   200
% 3.40/0.97  --lt_threshold                          2000
% 3.40/0.97  --clause_weak_htbl                      true
% 3.40/0.97  --gc_record_bc_elim                     false
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing Options
% 3.40/0.97  
% 3.40/0.97  --preprocessing_flag                    true
% 3.40/0.97  --time_out_prep_mult                    0.1
% 3.40/0.97  --splitting_mode                        input
% 3.40/0.97  --splitting_grd                         true
% 3.40/0.97  --splitting_cvd                         false
% 3.40/0.97  --splitting_cvd_svl                     false
% 3.40/0.97  --splitting_nvd                         32
% 3.40/0.97  --sub_typing                            true
% 3.40/0.97  --prep_gs_sim                           true
% 3.40/0.97  --prep_unflatten                        true
% 3.40/0.97  --prep_res_sim                          true
% 3.40/0.97  --prep_upred                            true
% 3.40/0.97  --prep_sem_filter                       exhaustive
% 3.40/0.97  --prep_sem_filter_out                   false
% 3.40/0.97  --pred_elim                             true
% 3.40/0.97  --res_sim_input                         true
% 3.40/0.97  --eq_ax_congr_red                       true
% 3.40/0.97  --pure_diseq_elim                       true
% 3.40/0.97  --brand_transform                       false
% 3.40/0.97  --non_eq_to_eq                          false
% 3.40/0.97  --prep_def_merge                        true
% 3.40/0.97  --prep_def_merge_prop_impl              false
% 3.40/0.97  --prep_def_merge_mbd                    true
% 3.40/0.97  --prep_def_merge_tr_red                 false
% 3.40/0.97  --prep_def_merge_tr_cl                  false
% 3.40/0.97  --smt_preprocessing                     true
% 3.40/0.97  --smt_ac_axioms                         fast
% 3.40/0.97  --preprocessed_out                      false
% 3.40/0.97  --preprocessed_stats                    false
% 3.40/0.97  
% 3.40/0.97  ------ Abstraction refinement Options
% 3.40/0.97  
% 3.40/0.97  --abstr_ref                             []
% 3.40/0.97  --abstr_ref_prep                        false
% 3.40/0.97  --abstr_ref_until_sat                   false
% 3.40/0.97  --abstr_ref_sig_restrict                funpre
% 3.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.97  --abstr_ref_under                       []
% 3.40/0.97  
% 3.40/0.97  ------ SAT Options
% 3.40/0.97  
% 3.40/0.97  --sat_mode                              false
% 3.40/0.97  --sat_fm_restart_options                ""
% 3.40/0.97  --sat_gr_def                            false
% 3.40/0.97  --sat_epr_types                         true
% 3.40/0.97  --sat_non_cyclic_types                  false
% 3.40/0.97  --sat_finite_models                     false
% 3.40/0.97  --sat_fm_lemmas                         false
% 3.40/0.97  --sat_fm_prep                           false
% 3.40/0.97  --sat_fm_uc_incr                        true
% 3.40/0.97  --sat_out_model                         small
% 3.40/0.97  --sat_out_clauses                       false
% 3.40/0.97  
% 3.40/0.97  ------ QBF Options
% 3.40/0.97  
% 3.40/0.97  --qbf_mode                              false
% 3.40/0.97  --qbf_elim_univ                         false
% 3.40/0.97  --qbf_dom_inst                          none
% 3.40/0.97  --qbf_dom_pre_inst                      false
% 3.40/0.97  --qbf_sk_in                             false
% 3.40/0.97  --qbf_pred_elim                         true
% 3.40/0.97  --qbf_split                             512
% 3.40/0.97  
% 3.40/0.97  ------ BMC1 Options
% 3.40/0.97  
% 3.40/0.97  --bmc1_incremental                      false
% 3.40/0.97  --bmc1_axioms                           reachable_all
% 3.40/0.97  --bmc1_min_bound                        0
% 3.40/0.97  --bmc1_max_bound                        -1
% 3.40/0.97  --bmc1_max_bound_default                -1
% 3.40/0.97  --bmc1_symbol_reachability              true
% 3.40/0.97  --bmc1_property_lemmas                  false
% 3.40/0.97  --bmc1_k_induction                      false
% 3.40/0.97  --bmc1_non_equiv_states                 false
% 3.40/0.97  --bmc1_deadlock                         false
% 3.40/0.97  --bmc1_ucm                              false
% 3.40/0.97  --bmc1_add_unsat_core                   none
% 3.40/0.97  --bmc1_unsat_core_children              false
% 3.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.97  --bmc1_out_stat                         full
% 3.40/0.97  --bmc1_ground_init                      false
% 3.40/0.97  --bmc1_pre_inst_next_state              false
% 3.40/0.97  --bmc1_pre_inst_state                   false
% 3.40/0.97  --bmc1_pre_inst_reach_state             false
% 3.40/0.97  --bmc1_out_unsat_core                   false
% 3.40/0.97  --bmc1_aig_witness_out                  false
% 3.40/0.97  --bmc1_verbose                          false
% 3.40/0.97  --bmc1_dump_clauses_tptp                false
% 3.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.97  --bmc1_dump_file                        -
% 3.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.97  --bmc1_ucm_extend_mode                  1
% 3.40/0.97  --bmc1_ucm_init_mode                    2
% 3.40/0.97  --bmc1_ucm_cone_mode                    none
% 3.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.97  --bmc1_ucm_relax_model                  4
% 3.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.97  --bmc1_ucm_layered_model                none
% 3.40/0.97  --bmc1_ucm_max_lemma_size               10
% 3.40/0.97  
% 3.40/0.97  ------ AIG Options
% 3.40/0.97  
% 3.40/0.97  --aig_mode                              false
% 3.40/0.97  
% 3.40/0.97  ------ Instantiation Options
% 3.40/0.97  
% 3.40/0.97  --instantiation_flag                    true
% 3.40/0.97  --inst_sos_flag                         true
% 3.40/0.97  --inst_sos_phase                        true
% 3.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.97  --inst_lit_sel_side                     none
% 3.40/0.97  --inst_solver_per_active                1400
% 3.40/0.97  --inst_solver_calls_frac                1.
% 3.40/0.97  --inst_passive_queue_type               priority_queues
% 3.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.97  --inst_passive_queues_freq              [25;2]
% 3.40/0.97  --inst_dismatching                      true
% 3.40/0.97  --inst_eager_unprocessed_to_passive     true
% 3.40/0.97  --inst_prop_sim_given                   true
% 3.40/0.97  --inst_prop_sim_new                     false
% 3.40/0.97  --inst_subs_new                         false
% 3.40/0.97  --inst_eq_res_simp                      false
% 3.40/0.97  --inst_subs_given                       false
% 3.40/0.97  --inst_orphan_elimination               true
% 3.40/0.97  --inst_learning_loop_flag               true
% 3.40/0.97  --inst_learning_start                   3000
% 3.40/0.97  --inst_learning_factor                  2
% 3.40/0.97  --inst_start_prop_sim_after_learn       3
% 3.40/0.97  --inst_sel_renew                        solver
% 3.40/0.97  --inst_lit_activity_flag                true
% 3.40/0.97  --inst_restr_to_given                   false
% 3.40/0.97  --inst_activity_threshold               500
% 3.40/0.97  --inst_out_proof                        true
% 3.40/0.97  
% 3.40/0.97  ------ Resolution Options
% 3.40/0.97  
% 3.40/0.97  --resolution_flag                       false
% 3.40/0.97  --res_lit_sel                           adaptive
% 3.40/0.97  --res_lit_sel_side                      none
% 3.40/0.97  --res_ordering                          kbo
% 3.40/0.97  --res_to_prop_solver                    active
% 3.40/0.97  --res_prop_simpl_new                    false
% 3.40/0.97  --res_prop_simpl_given                  true
% 3.40/0.97  --res_passive_queue_type                priority_queues
% 3.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.97  --res_passive_queues_freq               [15;5]
% 3.40/0.97  --res_forward_subs                      full
% 3.40/0.97  --res_backward_subs                     full
% 3.40/0.97  --res_forward_subs_resolution           true
% 3.40/0.97  --res_backward_subs_resolution          true
% 3.40/0.97  --res_orphan_elimination                true
% 3.40/0.97  --res_time_limit                        2.
% 3.40/0.97  --res_out_proof                         true
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Options
% 3.40/0.97  
% 3.40/0.97  --superposition_flag                    true
% 3.40/0.97  --sup_passive_queue_type                priority_queues
% 3.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.97  --demod_completeness_check              fast
% 3.40/0.97  --demod_use_ground                      true
% 3.40/0.97  --sup_to_prop_solver                    passive
% 3.40/0.97  --sup_prop_simpl_new                    true
% 3.40/0.97  --sup_prop_simpl_given                  true
% 3.40/0.97  --sup_fun_splitting                     true
% 3.40/0.97  --sup_smt_interval                      50000
% 3.40/0.97  
% 3.40/0.97  ------ Superposition Simplification Setup
% 3.40/0.97  
% 3.40/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.40/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.40/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.40/0.97  --sup_immed_triv                        [TrivRules]
% 3.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_immed_bw_main                     []
% 3.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.97  --sup_input_bw                          []
% 3.40/0.97  
% 3.40/0.97  ------ Combination Options
% 3.40/0.97  
% 3.40/0.97  --comb_res_mult                         3
% 3.40/0.97  --comb_sup_mult                         2
% 3.40/0.97  --comb_inst_mult                        10
% 3.40/0.97  
% 3.40/0.97  ------ Debug Options
% 3.40/0.97  
% 3.40/0.97  --dbg_backtrace                         false
% 3.40/0.97  --dbg_dump_prop_clauses                 false
% 3.40/0.97  --dbg_dump_prop_clauses_file            -
% 3.40/0.97  --dbg_out_stat                          false
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  ------ Proving...
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  % SZS status Theorem for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  fof(f19,conjecture,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f20,negated_conjecture,(
% 3.40/0.97    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.40/0.97    inference(negated_conjecture,[],[f19])).
% 3.40/0.97  
% 3.40/0.97  fof(f43,plain,(
% 3.40/0.97    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f20])).
% 3.40/0.97  
% 3.40/0.97  fof(f44,plain,(
% 3.40/0.97    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f43])).
% 3.40/0.97  
% 3.40/0.97  fof(f55,plain,(
% 3.40/0.97    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.40/0.97    introduced(choice_axiom,[])).
% 3.40/0.97  
% 3.40/0.97  fof(f54,plain,(
% 3.40/0.97    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.40/0.97    introduced(choice_axiom,[])).
% 3.40/0.97  
% 3.40/0.97  fof(f56,plain,(
% 3.40/0.97    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f55,f54])).
% 3.40/0.97  
% 3.40/0.97  fof(f91,plain,(
% 3.40/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f16,axiom,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f37,plain,(
% 3.40/0.97    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f16])).
% 3.40/0.97  
% 3.40/0.97  fof(f38,plain,(
% 3.40/0.97    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f37])).
% 3.40/0.97  
% 3.40/0.97  fof(f84,plain,(
% 3.40/0.97    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f38])).
% 3.40/0.97  
% 3.40/0.97  fof(f96,plain,(
% 3.40/0.97    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f13,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f31,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(ennf_transformation,[],[f13])).
% 3.40/0.97  
% 3.40/0.97  fof(f32,plain,(
% 3.40/0.97    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(flattening,[],[f31])).
% 3.40/0.97  
% 3.40/0.97  fof(f77,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f32])).
% 3.40/0.97  
% 3.40/0.97  fof(f14,axiom,(
% 3.40/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f33,plain,(
% 3.40/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f14])).
% 3.40/0.97  
% 3.40/0.97  fof(f34,plain,(
% 3.40/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.40/0.97    inference(flattening,[],[f33])).
% 3.40/0.97  
% 3.40/0.97  fof(f53,plain,(
% 3.40/0.97    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.40/0.97    inference(nnf_transformation,[],[f34])).
% 3.40/0.97  
% 3.40/0.97  fof(f78,plain,(
% 3.40/0.97    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f53])).
% 3.40/0.97  
% 3.40/0.97  fof(f9,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f21,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.40/0.97    inference(pure_predicate_removal,[],[f9])).
% 3.40/0.97  
% 3.40/0.97  fof(f26,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(ennf_transformation,[],[f21])).
% 3.40/0.97  
% 3.40/0.97  fof(f70,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f26])).
% 3.40/0.97  
% 3.40/0.97  fof(f88,plain,(
% 3.40/0.97    v1_funct_1(sK2)),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f90,plain,(
% 3.40/0.97    v3_funct_2(sK2,sK1,sK1)),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f8,axiom,(
% 3.40/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f69,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f8])).
% 3.40/0.97  
% 3.40/0.97  fof(f5,axiom,(
% 3.40/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f51,plain,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.40/0.97    inference(nnf_transformation,[],[f5])).
% 3.40/0.97  
% 3.40/0.97  fof(f65,plain,(
% 3.40/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f51])).
% 3.40/0.97  
% 3.40/0.97  fof(f7,axiom,(
% 3.40/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f25,plain,(
% 3.40/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.40/0.97    inference(ennf_transformation,[],[f7])).
% 3.40/0.97  
% 3.40/0.97  fof(f68,plain,(
% 3.40/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f25])).
% 3.40/0.97  
% 3.40/0.97  fof(f66,plain,(
% 3.40/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f51])).
% 3.40/0.97  
% 3.40/0.97  fof(f11,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f28,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(ennf_transformation,[],[f11])).
% 3.40/0.97  
% 3.40/0.97  fof(f72,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f28])).
% 3.40/0.97  
% 3.40/0.97  fof(f18,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f41,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.40/0.97    inference(ennf_transformation,[],[f18])).
% 3.40/0.97  
% 3.40/0.97  fof(f42,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.40/0.97    inference(flattening,[],[f41])).
% 3.40/0.97  
% 3.40/0.97  fof(f87,plain,(
% 3.40/0.97    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f42])).
% 3.40/0.97  
% 3.40/0.97  fof(f17,axiom,(
% 3.40/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f39,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.40/0.97    inference(ennf_transformation,[],[f17])).
% 3.40/0.97  
% 3.40/0.97  fof(f40,plain,(
% 3.40/0.97    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.40/0.97    inference(flattening,[],[f39])).
% 3.40/0.97  
% 3.40/0.97  fof(f85,plain,(
% 3.40/0.97    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f40])).
% 3.40/0.97  
% 3.40/0.97  fof(f89,plain,(
% 3.40/0.97    v1_funct_2(sK2,sK1,sK1)),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f2,axiom,(
% 3.40/0.97    v1_xboole_0(k1_xboole_0)),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f60,plain,(
% 3.40/0.97    v1_xboole_0(k1_xboole_0)),
% 3.40/0.97    inference(cnf_transformation,[],[f2])).
% 3.40/0.97  
% 3.40/0.97  fof(f95,plain,(
% 3.40/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f10,axiom,(
% 3.40/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f27,plain,(
% 3.40/0.97    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.40/0.97    inference(ennf_transformation,[],[f10])).
% 3.40/0.97  
% 3.40/0.97  fof(f71,plain,(
% 3.40/0.97    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f27])).
% 3.40/0.97  
% 3.40/0.97  fof(f97,plain,(
% 3.40/0.97    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f12,axiom,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f29,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.40/0.97    inference(ennf_transformation,[],[f12])).
% 3.40/0.97  
% 3.40/0.97  fof(f30,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(flattening,[],[f29])).
% 3.40/0.97  
% 3.40/0.97  fof(f52,plain,(
% 3.40/0.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.40/0.97    inference(nnf_transformation,[],[f30])).
% 3.40/0.97  
% 3.40/0.97  fof(f74,plain,(
% 3.40/0.97    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(cnf_transformation,[],[f52])).
% 3.40/0.97  
% 3.40/0.97  fof(f100,plain,(
% 3.40/0.97    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.40/0.97    inference(equality_resolution,[],[f74])).
% 3.40/0.97  
% 3.40/0.97  fof(f15,axiom,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f35,plain,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.40/0.97    inference(ennf_transformation,[],[f15])).
% 3.40/0.97  
% 3.40/0.97  fof(f36,plain,(
% 3.40/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.40/0.97    inference(flattening,[],[f35])).
% 3.40/0.97  
% 3.40/0.97  fof(f83,plain,(
% 3.40/0.97    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f36])).
% 3.40/0.97  
% 3.40/0.97  fof(f3,axiom,(
% 3.40/0.97    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.97  
% 3.40/0.97  fof(f23,plain,(
% 3.40/0.97    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.40/0.97    inference(ennf_transformation,[],[f3])).
% 3.40/0.97  
% 3.40/0.97  fof(f61,plain,(
% 3.40/0.97    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.40/0.97    inference(cnf_transformation,[],[f23])).
% 3.40/0.97  
% 3.40/0.97  fof(f92,plain,(
% 3.40/0.97    v1_funct_1(sK3)),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  fof(f93,plain,(
% 3.40/0.97    v1_funct_2(sK3,sK1,sK1)),
% 3.40/0.97    inference(cnf_transformation,[],[f56])).
% 3.40/0.97  
% 3.40/0.97  cnf(c_37,negated_conjecture,
% 3.40/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2445,plain,
% 3.40/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_27,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2452,plain,
% 3.40/0.97      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.40/0.97      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.40/0.97      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.40/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.40/0.97      | v1_funct_1(X1) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6560,plain,
% 3.40/0.97      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.40/0.97      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2445,c_2452]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_32,negated_conjecture,
% 3.40/0.97      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f96]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2450,plain,
% 3.40/0.97      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_18,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | v2_funct_2(X0,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f77]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_22,plain,
% 3.40/0.97      ( ~ v2_funct_2(X0,X1)
% 3.40/0.97      | ~ v5_relat_1(X0,X1)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X1 ),
% 3.40/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_537,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ v5_relat_1(X3,X4)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X3)
% 3.40/0.97      | X3 != X0
% 3.40/0.97      | X4 != X2
% 3.40/0.97      | k2_relat_1(X3) = X4 ),
% 3.40/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_538,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ v5_relat_1(X0,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X2 ),
% 3.40/0.97      inference(unflattening,[status(thm)],[c_537]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_13,plain,
% 3.40/0.97      ( v5_relat_1(X0,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_554,plain,
% 3.40/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_funct_1(X0)
% 3.40/0.97      | ~ v1_relat_1(X0)
% 3.40/0.97      | k2_relat_1(X0) = X2 ),
% 3.40/0.97      inference(forward_subsumption_resolution,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_538,c_13]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2438,plain,
% 3.40/0.97      ( k2_relat_1(X0) = X1
% 3.40/0.97      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0) != iProver_top
% 3.40/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3979,plain,
% 3.40/0.97      ( k2_relat_1(sK2) = sK1
% 3.40/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top
% 3.40/0.97      | v1_relat_1(sK2) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2445,c_2438]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_40,negated_conjecture,
% 3.40/0.97      ( v1_funct_1(sK2) ),
% 3.40/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_41,plain,
% 3.40/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_38,negated_conjecture,
% 3.40/0.97      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_43,plain,
% 3.40/0.97      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_12,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_101,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_103,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_101]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_9,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2462,plain,
% 3.40/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.40/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3278,plain,
% 3.40/0.97      ( r1_tarski(sK2,k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2445,c_2462]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_11,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/0.97      | ~ v1_relat_1(X1)
% 3.40/0.97      | v1_relat_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_8,plain,
% 3.40/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_293,plain,
% 3.40/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.40/0.97      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_294,plain,
% 3.40/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_293]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_368,plain,
% 3.40/0.97      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.40/0.97      inference(bin_hyper_res,[status(thm)],[c_11,c_294]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2439,plain,
% 3.40/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.40/0.97      | v1_relat_1(X1) != iProver_top
% 3.40/0.97      | v1_relat_1(X0) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3819,plain,
% 3.40/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.40/0.97      | v1_relat_1(sK2) = iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_3278,c_2439]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4790,plain,
% 3.40/0.97      ( k2_relat_1(sK2) = sK1 ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_3979,c_41,c_43,c_103,c_3819]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_15,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2459,plain,
% 3.40/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4253,plain,
% 3.40/0.97      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2445,c_2459]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4792,plain,
% 3.40/0.97      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.40/0.97      inference(demodulation,[status(thm)],[c_4790,c_4253]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_30,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.40/0.97      | ~ v1_funct_2(X3,X1,X0)
% 3.40/0.97      | ~ v1_funct_2(X2,X0,X1)
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.40/0.97      | ~ v2_funct_1(X2)
% 3.40/0.97      | ~ v1_funct_1(X2)
% 3.40/0.97      | ~ v1_funct_1(X3)
% 3.40/0.97      | k2_relset_1(X0,X1,X2) != X1
% 3.40/0.97      | k2_funct_1(X2) = X3
% 3.40/0.97      | k1_xboole_0 = X1
% 3.40/0.97      | k1_xboole_0 = X0 ),
% 3.40/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_29,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.40/0.97      | ~ v1_funct_2(X3,X1,X0)
% 3.40/0.97      | ~ v1_funct_2(X2,X0,X1)
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.40/0.97      | v2_funct_1(X2)
% 3.40/0.97      | ~ v1_funct_1(X2)
% 3.40/0.97      | ~ v1_funct_1(X3) ),
% 3.40/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_215,plain,
% 3.40/0.97      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ v1_funct_2(X2,X0,X1)
% 3.40/0.97      | ~ v1_funct_2(X3,X1,X0)
% 3.40/0.97      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.40/0.97      | ~ v1_funct_1(X2)
% 3.40/0.97      | ~ v1_funct_1(X3)
% 3.40/0.97      | k2_relset_1(X0,X1,X2) != X1
% 3.40/0.97      | k2_funct_1(X2) = X3
% 3.40/0.97      | k1_xboole_0 = X1
% 3.40/0.97      | k1_xboole_0 = X0 ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_30,c_29]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_216,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.40/0.97      | ~ v1_funct_2(X3,X1,X0)
% 3.40/0.97      | ~ v1_funct_2(X2,X0,X1)
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.40/0.97      | ~ v1_funct_1(X3)
% 3.40/0.97      | ~ v1_funct_1(X2)
% 3.40/0.97      | k2_relset_1(X0,X1,X2) != X1
% 3.40/0.97      | k2_funct_1(X2) = X3
% 3.40/0.97      | k1_xboole_0 = X1
% 3.40/0.97      | k1_xboole_0 = X0 ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_215]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2441,plain,
% 3.40/0.97      ( k2_relset_1(X0,X1,X2) != X1
% 3.40/0.97      | k2_funct_1(X2) = X3
% 3.40/0.97      | k1_xboole_0 = X1
% 3.40/0.97      | k1_xboole_0 = X0
% 3.40/0.97      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.40/0.97      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.40/0.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.40/0.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.40/0.97      | v1_funct_1(X2) != iProver_top
% 3.40/0.97      | v1_funct_1(X3) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5076,plain,
% 3.40/0.97      ( k2_funct_1(sK2) = X0
% 3.40/0.97      | sK1 = k1_xboole_0
% 3.40/0.97      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.40/0.97      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.40/0.97      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_4792,c_2441]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_39,negated_conjecture,
% 3.40/0.97      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_42,plain,
% 3.40/0.97      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_44,plain,
% 3.40/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3,plain,
% 3.40/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_120,plain,
% 3.40/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1671,plain,
% 3.40/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.40/0.97      theory(equality) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2891,plain,
% 3.40/0.97      ( v1_xboole_0(X0)
% 3.40/0.97      | ~ v1_xboole_0(k1_xboole_0)
% 3.40/0.97      | X0 != k1_xboole_0 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1671]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2892,plain,
% 3.40/0.97      ( X0 != k1_xboole_0
% 3.40/0.97      | v1_xboole_0(X0) = iProver_top
% 3.40/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_2891]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2894,plain,
% 3.40/0.97      ( sK1 != k1_xboole_0
% 3.40/0.97      | v1_xboole_0(sK1) = iProver_top
% 3.40/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2892]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_33,negated_conjecture,
% 3.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f95]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2449,plain,
% 3.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_14,plain,
% 3.40/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.40/0.97      | ~ v1_xboole_0(X1)
% 3.40/0.97      | v1_xboole_0(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2460,plain,
% 3.40/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.40/0.97      | v1_xboole_0(X1) != iProver_top
% 3.40/0.97      | v1_xboole_0(X0) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5142,plain,
% 3.40/0.97      ( v1_xboole_0(sK3) = iProver_top
% 3.40/0.97      | v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2449,c_2460]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_48,plain,
% 3.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_31,negated_conjecture,
% 3.40/0.97      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.40/0.97      inference(cnf_transformation,[],[f97]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1668,plain,( X0 = X0 ),theory(equality) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1697,plain,
% 3.40/0.97      ( sK1 = sK1 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1668]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_16,plain,
% 3.40/0.97      ( r2_relset_1(X0,X1,X2,X2)
% 3.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.40/0.97      inference(cnf_transformation,[],[f100]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2535,plain,
% 3.40/0.97      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.40/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_16]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_1676,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.40/0.97      | r2_relset_1(X4,X5,X6,X7)
% 3.40/0.97      | X5 != X1
% 3.40/0.97      | X4 != X0
% 3.40/0.97      | X6 != X2
% 3.40/0.97      | X7 != X3 ),
% 3.40/0.97      theory(equality) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2511,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.40/0.97      | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.40/0.97      | k2_funct_2(sK1,sK2) != X3
% 3.40/0.97      | sK3 != X2
% 3.40/0.97      | sK1 != X1
% 3.40/0.97      | sK1 != X0 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1676]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2700,plain,
% 3.40/0.97      ( ~ r2_relset_1(X0,X1,sK3,X2)
% 3.40/0.97      | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.40/0.97      | k2_funct_2(sK1,sK2) != X2
% 3.40/0.97      | sK3 != sK3
% 3.40/0.97      | sK1 != X1
% 3.40/0.97      | sK1 != X0 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2511]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2702,plain,
% 3.40/0.97      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.40/0.97      | ~ r2_relset_1(sK1,sK1,sK3,sK1)
% 3.40/0.97      | k2_funct_2(sK1,sK2) != sK1
% 3.40/0.97      | sK3 != sK3
% 3.40/0.97      | sK1 != sK1 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2700]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2708,plain,
% 3.40/0.97      ( sK3 = sK3 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1668]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_23,plain,
% 3.40/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.40/0.97      | ~ v1_funct_1(X0) ),
% 3.40/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2871,plain,
% 3.40/0.97      ( ~ v1_funct_2(sK2,X0,X0)
% 3.40/0.97      | ~ v3_funct_2(sK2,X0,X0)
% 3.40/0.97      | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.40/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.40/0.97      | ~ v1_funct_1(sK2) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_23]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2872,plain,
% 3.40/0.97      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 3.40/0.97      | v3_funct_2(sK2,X0,X0) != iProver_top
% 3.40/0.97      | m1_subset_1(k2_funct_2(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top
% 3.40/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_2871]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2874,plain,
% 3.40/0.97      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.40/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2872]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4,plain,
% 3.40/0.97      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.40/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2924,plain,
% 3.40/0.97      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | X0 = sK3 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2925,plain,
% 3.40/0.97      ( X0 = sK3
% 3.40/0.97      | v1_xboole_0(X0) != iProver_top
% 3.40/0.97      | v1_xboole_0(sK3) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2927,plain,
% 3.40/0.97      ( sK1 = sK3
% 3.40/0.97      | v1_xboole_0(sK3) != iProver_top
% 3.40/0.97      | v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2925]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2977,plain,
% 3.40/0.97      ( ~ v1_xboole_0(X0)
% 3.40/0.97      | ~ v1_xboole_0(k2_funct_2(sK1,sK2))
% 3.40/0.97      | k2_funct_2(sK1,sK2) = X0 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2978,plain,
% 3.40/0.97      ( k2_funct_2(sK1,sK2) = X0
% 3.40/0.97      | v1_xboole_0(X0) != iProver_top
% 3.40/0.97      | v1_xboole_0(k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_2977]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2980,plain,
% 3.40/0.97      ( k2_funct_2(sK1,sK2) = sK1
% 3.40/0.97      | v1_xboole_0(k2_funct_2(sK1,sK2)) != iProver_top
% 3.40/0.97      | v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2978]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2637,plain,
% 3.40/0.97      ( r2_relset_1(X0,X1,X2,X3)
% 3.40/0.97      | ~ r2_relset_1(sK1,sK1,sK3,sK3)
% 3.40/0.97      | X2 != sK3
% 3.40/0.97      | X3 != sK3
% 3.40/0.97      | X0 != sK1
% 3.40/0.97      | X1 != sK1 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_1676]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3003,plain,
% 3.40/0.97      ( r2_relset_1(X0,X1,sK3,X2)
% 3.40/0.97      | ~ r2_relset_1(sK1,sK1,sK3,sK3)
% 3.40/0.97      | X2 != sK3
% 3.40/0.97      | X0 != sK1
% 3.40/0.97      | X1 != sK1
% 3.40/0.97      | sK3 != sK3 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_3010,plain,
% 3.40/0.97      ( ~ r2_relset_1(sK1,sK1,sK3,sK3)
% 3.40/0.97      | r2_relset_1(sK1,sK1,sK3,sK1)
% 3.40/0.97      | sK3 != sK3
% 3.40/0.97      | sK1 != sK3
% 3.40/0.97      | sK1 != sK1 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4047,plain,
% 3.40/0.97      ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ v1_xboole_0(X0)
% 3.40/0.97      | v1_xboole_0(k2_funct_2(sK1,sK2)) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4048,plain,
% 3.40/0.97      ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.40/0.97      | v1_xboole_0(X0) != iProver_top
% 3.40/0.97      | v1_xboole_0(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_4047]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4050,plain,
% 3.40/0.97      ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_xboole_0(k2_funct_2(sK1,sK2)) = iProver_top
% 3.40/0.97      | v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_4048]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4052,plain,
% 3.40/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.40/0.97      | ~ v1_xboole_0(X0)
% 3.40/0.97      | v1_xboole_0(sK3) ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4053,plain,
% 3.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.40/0.97      | v1_xboole_0(X0) != iProver_top
% 3.40/0.97      | v1_xboole_0(sK3) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_4052]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_4055,plain,
% 3.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_xboole_0(sK3) = iProver_top
% 3.40/0.97      | v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_4053]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5206,plain,
% 3.40/0.97      ( v1_xboole_0(sK1) != iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_5142,c_41,c_42,c_43,c_44,c_33,c_48,c_31,c_1697,c_2535,
% 3.40/0.97                 c_2702,c_2708,c_2874,c_2927,c_2980,c_3010,c_4050,c_4055]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5275,plain,
% 3.40/0.97      ( v1_funct_1(X0) != iProver_top
% 3.40/0.97      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.40/0.97      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.40/0.97      | k2_funct_1(sK2) = X0
% 3.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_5076,c_41,c_42,c_43,c_44,c_33,c_48,c_31,c_120,c_1697,
% 3.40/0.97                 c_2535,c_2702,c_2708,c_2874,c_2894,c_2927,c_2980,c_3010,
% 3.40/0.97                 c_4050,c_4055]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5276,plain,
% 3.40/0.97      ( k2_funct_1(sK2) = X0
% 3.40/0.97      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.40/0.97      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.40/0.97      inference(renaming,[status(thm)],[c_5275]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5281,plain,
% 3.40/0.97      ( k2_funct_1(sK2) = sK3
% 3.40/0.97      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.40/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.40/0.97      | v1_funct_1(sK3) != iProver_top ),
% 3.40/0.97      inference(superposition,[status(thm)],[c_2450,c_5276]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_36,negated_conjecture,
% 3.40/0.97      ( v1_funct_1(sK3) ),
% 3.40/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_45,plain,
% 3.40/0.97      ( v1_funct_1(sK3) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_35,negated_conjecture,
% 3.40/0.97      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.40/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_46,plain,
% 3.40/0.97      ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
% 3.40/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_5410,plain,
% 3.40/0.97      ( k2_funct_1(sK2) = sK3 ),
% 3.40/0.97      inference(global_propositional_subsumption,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_5281,c_45,c_46,c_48]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_6563,plain,
% 3.40/0.97      ( k2_funct_2(sK1,sK2) = sK3
% 3.40/0.97      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.40/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.40/0.97      inference(light_normalisation,[status(thm)],[c_6560,c_5410]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(c_2563,plain,
% 3.40/0.97      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.40/0.97      | ~ r2_relset_1(sK1,sK1,sK3,sK3)
% 3.40/0.97      | k2_funct_2(sK1,sK2) != sK3
% 3.40/0.97      | sK3 != sK3
% 3.40/0.97      | sK1 != sK1 ),
% 3.40/0.97      inference(instantiation,[status(thm)],[c_2511]) ).
% 3.40/0.97  
% 3.40/0.97  cnf(contradiction,plain,
% 3.40/0.97      ( $false ),
% 3.40/0.97      inference(minisat,
% 3.40/0.97                [status(thm)],
% 3.40/0.97                [c_6563,c_2708,c_2563,c_2535,c_1697,c_31,c_33,c_43,c_42,
% 3.40/0.97                 c_41]) ).
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.97  
% 3.40/0.97  ------                               Statistics
% 3.40/0.97  
% 3.40/0.97  ------ General
% 3.40/0.97  
% 3.40/0.97  abstr_ref_over_cycles:                  0
% 3.40/0.97  abstr_ref_under_cycles:                 0
% 3.40/0.97  gc_basic_clause_elim:                   0
% 3.40/0.97  forced_gc_time:                         0
% 3.40/0.97  parsing_time:                           0.01
% 3.40/0.97  unif_index_cands_time:                  0.
% 3.40/0.97  unif_index_add_time:                    0.
% 3.40/0.97  orderings_time:                         0.
% 3.40/0.97  out_proof_time:                         0.011
% 3.40/0.97  total_time:                             0.237
% 3.40/0.97  num_of_symbols:                         56
% 3.40/0.97  num_of_terms:                           7103
% 3.40/0.97  
% 3.40/0.97  ------ Preprocessing
% 3.40/0.97  
% 3.40/0.97  num_of_splits:                          0
% 3.40/0.97  num_of_split_atoms:                     0
% 3.40/0.97  num_of_reused_defs:                     0
% 3.40/0.97  num_eq_ax_congr_red:                    33
% 3.40/0.97  num_of_sem_filtered_clauses:            3
% 3.40/0.97  num_of_subtypes:                        0
% 3.40/0.97  monotx_restored_types:                  0
% 3.40/0.97  sat_num_of_epr_types:                   0
% 3.40/0.97  sat_num_of_non_cyclic_types:            0
% 3.40/0.97  sat_guarded_non_collapsed_types:        0
% 3.40/0.97  num_pure_diseq_elim:                    0
% 3.40/0.97  simp_replaced_by:                       0
% 3.40/0.97  res_preprocessed:                       176
% 3.40/0.97  prep_upred:                             0
% 3.40/0.97  prep_unflattend:                        70
% 3.40/0.97  smt_new_axioms:                         0
% 3.40/0.97  pred_elim_cands:                        9
% 3.40/0.97  pred_elim:                              2
% 3.40/0.97  pred_elim_cl:                           3
% 3.40/0.97  pred_elim_cycles:                       7
% 3.40/0.97  merged_defs:                            8
% 3.40/0.97  merged_defs_ncl:                        0
% 3.40/0.97  bin_hyper_res:                          10
% 3.40/0.97  prep_cycles:                            4
% 3.40/0.97  pred_elim_time:                         0.021
% 3.40/0.97  splitting_time:                         0.
% 3.40/0.97  sem_filter_time:                        0.
% 3.40/0.97  monotx_time:                            0.001
% 3.40/0.97  subtype_inf_time:                       0.
% 3.40/0.97  
% 3.40/0.97  ------ Problem properties
% 3.40/0.97  
% 3.40/0.97  clauses:                                35
% 3.40/0.97  conjectures:                            10
% 3.40/0.97  epr:                                    11
% 3.40/0.97  horn:                                   32
% 3.40/0.97  ground:                                 11
% 3.40/0.97  unary:                                  14
% 3.40/0.97  binary:                                 6
% 3.40/0.97  lits:                                   98
% 3.40/0.97  lits_eq:                                15
% 3.40/0.97  fd_pure:                                0
% 3.40/0.97  fd_pseudo:                              0
% 3.40/0.97  fd_cond:                                1
% 3.40/0.97  fd_pseudo_cond:                         5
% 3.40/0.97  ac_symbols:                             0
% 3.40/0.97  
% 3.40/0.97  ------ Propositional Solver
% 3.40/0.97  
% 3.40/0.97  prop_solver_calls:                      29
% 3.40/0.97  prop_fast_solver_calls:                 1459
% 3.40/0.97  smt_solver_calls:                       0
% 3.40/0.97  smt_fast_solver_calls:                  0
% 3.40/0.97  prop_num_of_clauses:                    2271
% 3.40/0.97  prop_preprocess_simplified:             7803
% 3.40/0.97  prop_fo_subsumed:                       31
% 3.40/0.97  prop_solver_time:                       0.
% 3.40/0.97  smt_solver_time:                        0.
% 3.40/0.97  smt_fast_solver_time:                   0.
% 3.40/0.97  prop_fast_solver_time:                  0.
% 3.40/0.97  prop_unsat_core_time:                   0.
% 3.40/0.97  
% 3.40/0.97  ------ QBF
% 3.40/0.97  
% 3.40/0.97  qbf_q_res:                              0
% 3.40/0.97  qbf_num_tautologies:                    0
% 3.40/0.97  qbf_prep_cycles:                        0
% 3.40/0.97  
% 3.40/0.97  ------ BMC1
% 3.40/0.97  
% 3.40/0.97  bmc1_current_bound:                     -1
% 3.40/0.97  bmc1_last_solved_bound:                 -1
% 3.40/0.97  bmc1_unsat_core_size:                   -1
% 3.40/0.97  bmc1_unsat_core_parents_size:           -1
% 3.40/0.97  bmc1_merge_next_fun:                    0
% 3.40/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.40/0.97  
% 3.40/0.97  ------ Instantiation
% 3.40/0.97  
% 3.40/0.97  inst_num_of_clauses:                    620
% 3.40/0.97  inst_num_in_passive:                    78
% 3.40/0.97  inst_num_in_active:                     320
% 3.40/0.97  inst_num_in_unprocessed:                222
% 3.40/0.97  inst_num_of_loops:                      360
% 3.40/0.97  inst_num_of_learning_restarts:          0
% 3.40/0.97  inst_num_moves_active_passive:          36
% 3.40/0.97  inst_lit_activity:                      0
% 3.40/0.97  inst_lit_activity_moves:                0
% 3.40/0.97  inst_num_tautologies:                   0
% 3.40/0.97  inst_num_prop_implied:                  0
% 3.40/0.97  inst_num_existing_simplified:           0
% 3.40/0.97  inst_num_eq_res_simplified:             0
% 3.40/0.97  inst_num_child_elim:                    0
% 3.40/0.97  inst_num_of_dismatching_blockings:      316
% 3.40/0.97  inst_num_of_non_proper_insts:           968
% 3.40/0.97  inst_num_of_duplicates:                 0
% 3.40/0.97  inst_inst_num_from_inst_to_res:         0
% 3.40/0.97  inst_dismatching_checking_time:         0.
% 3.40/0.97  
% 3.40/0.97  ------ Resolution
% 3.40/0.97  
% 3.40/0.97  res_num_of_clauses:                     0
% 3.40/0.97  res_num_in_passive:                     0
% 3.40/0.97  res_num_in_active:                      0
% 3.40/0.97  res_num_of_loops:                       180
% 3.40/0.97  res_forward_subset_subsumed:            29
% 3.40/0.97  res_backward_subset_subsumed:           0
% 3.40/0.97  res_forward_subsumed:                   0
% 3.40/0.97  res_backward_subsumed:                  0
% 3.40/0.97  res_forward_subsumption_resolution:     2
% 3.40/0.97  res_backward_subsumption_resolution:    0
% 3.40/0.97  res_clause_to_clause_subsumption:       207
% 3.40/0.97  res_orphan_elimination:                 0
% 3.40/0.97  res_tautology_del:                      62
% 3.40/0.97  res_num_eq_res_simplified:              0
% 3.40/0.97  res_num_sel_changes:                    0
% 3.40/0.97  res_moves_from_active_to_pass:          0
% 3.40/0.97  
% 3.40/0.97  ------ Superposition
% 3.40/0.97  
% 3.40/0.97  sup_time_total:                         0.
% 3.40/0.97  sup_time_generating:                    0.
% 3.40/0.97  sup_time_sim_full:                      0.
% 3.40/0.97  sup_time_sim_immed:                     0.
% 3.40/0.97  
% 3.40/0.97  sup_num_of_clauses:                     98
% 3.40/0.97  sup_num_in_active:                      68
% 3.40/0.97  sup_num_in_passive:                     30
% 3.40/0.97  sup_num_of_loops:                       70
% 3.40/0.97  sup_fw_superposition:                   76
% 3.40/0.97  sup_bw_superposition:                   3
% 3.40/0.97  sup_immediate_simplified:               7
% 3.40/0.97  sup_given_eliminated:                   0
% 3.40/0.97  comparisons_done:                       0
% 3.40/0.97  comparisons_avoided:                    0
% 3.40/0.97  
% 3.40/0.97  ------ Simplifications
% 3.40/0.97  
% 3.40/0.97  
% 3.40/0.97  sim_fw_subset_subsumed:                 2
% 3.40/0.97  sim_bw_subset_subsumed:                 1
% 3.40/0.97  sim_fw_subsumed:                        0
% 3.40/0.97  sim_bw_subsumed:                        1
% 3.40/0.97  sim_fw_subsumption_res:                 0
% 3.40/0.97  sim_bw_subsumption_res:                 0
% 3.40/0.97  sim_tautology_del:                      2
% 3.40/0.97  sim_eq_tautology_del:                   6
% 3.40/0.97  sim_eq_res_simp:                        0
% 3.40/0.97  sim_fw_demodulated:                     2
% 3.40/0.97  sim_bw_demodulated:                     2
% 3.40/0.97  sim_light_normalised:                   2
% 3.40/0.97  sim_joinable_taut:                      0
% 3.40/0.97  sim_joinable_simp:                      0
% 3.40/0.97  sim_ac_normalised:                      0
% 3.40/0.97  sim_smt_subsumption:                    0
% 3.40/0.97  
%------------------------------------------------------------------------------
