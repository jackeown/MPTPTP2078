%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:06 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 903 expanded)
%              Number of clauses        :  109 ( 278 expanded)
%              Number of leaves         :   22 ( 231 expanded)
%              Depth                    :   16
%              Number of atoms          :  697 (6264 expanded)
%              Number of equality atoms :  274 ( 608 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f57,f56])).

fof(f100,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f91,plain,(
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

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f89,plain,(
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

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f93,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f75,f88])).

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

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2400,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2410,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | v2_funct_2(X0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6052,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v2_funct_2(sK2,sK1) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_2410])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6396,plain,
    ( v2_funct_2(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6052,c_42,c_44])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_546,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_558,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_546,c_10])).

cnf(c_2390,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_4175,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_2(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_2390])).

cnf(c_6400,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_6396,c_4175])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2414,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4433,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2395,c_2414])).

cnf(c_6470,plain,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_6400,c_4433])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_223,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_30])).

cnf(c_224,plain,
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
    inference(renaming,[status(thm)],[c_223])).

cnf(c_2391,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_7175,plain,
    ( k2_funct_1(sK2) = X0
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6470,c_2391])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_126,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1591,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2939,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_2940,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2939])).

cnf(c_2942,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2940])).

cnf(c_5097,plain,
    ( k2_funct_1(sK2) = X0
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4433,c_2391])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5438,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | sK1 = k1_xboole_0
    | k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5097,c_42,c_43,c_45])).

cnf(c_5439,plain,
    ( k2_funct_1(sK2) = X0
    | k2_relat_1(sK2) != sK1
    | sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5438])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2403,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7391,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2395,c_2403])).

cnf(c_3688,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_7655,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7391,c_41,c_40,c_39,c_38,c_3688])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2407,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8350,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7655,c_2407])).

cnf(c_9051,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8350,c_42,c_43,c_44,c_45])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9057,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9051,c_2415])).

cnf(c_32,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_96,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_95,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_97,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_1588,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1617,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_1595,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X5 != X1
    | X4 != X0
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2467,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) != X3
    | sK3 != X2
    | sK1 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_2469,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | ~ r2_relset_1(sK1,sK1,sK1,sK1)
    | k2_funct_2(sK1,sK2) != sK1
    | sK3 != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2502,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2504,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_2502])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2543,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_2545,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_2620,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X4))
    | X1 != X4
    | X0 != X4
    | X2 != k6_partfun1(X4)
    | X3 != k6_partfun1(X4) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_2622,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | r2_relset_1(sK1,sK1,sK1,sK1)
    | sK1 != k6_partfun1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2670,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2671,plain,
    ( sK3 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_2673,plain,
    ( sK3 = sK1
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_3278,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(sK1))
    | X0 = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3279,plain,
    ( X0 = k6_partfun1(sK1)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3278])).

cnf(c_3281,plain,
    ( sK1 = k6_partfun1(sK1)
    | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3279])).

cnf(c_1589,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3008,plain,
    ( X0 != X1
    | k2_funct_2(sK1,sK2) != X1
    | k2_funct_2(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_3699,plain,
    ( X0 != k2_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = X0
    | k2_funct_2(sK1,sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3008])).

cnf(c_3700,plain,
    ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = sK1
    | sK1 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3699])).

cnf(c_5601,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_funct_1(sK2))
    | X0 = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5602,plain,
    ( X0 = k2_funct_1(sK2)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5601])).

cnf(c_5604,plain,
    ( sK1 = k2_funct_1(sK2)
    | v1_xboole_0(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5602])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2399,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5883,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2399,c_2415])).

cnf(c_10586,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9057,c_41,c_40,c_39,c_38,c_32,c_96,c_97,c_1617,c_2469,c_2504,c_2545,c_2622,c_2673,c_3281,c_3688,c_3700,c_5604,c_5883])).

cnf(c_14018,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | k2_funct_1(sK2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7175,c_41,c_42,c_40,c_43,c_39,c_44,c_38,c_45,c_32,c_96,c_97,c_126,c_1617,c_2469,c_2504,c_2545,c_2622,c_2673,c_2942,c_3281,c_3688,c_3700,c_4175,c_5097,c_5604,c_5883,c_6052,c_9057])).

cnf(c_14019,plain,
    ( k2_funct_1(sK2) = X0
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
    | v1_funct_2(X0,sK1,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14018])).

cnf(c_14024,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_2(sK3,sK1,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_14019])).

cnf(c_3170,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,sK3,X6)
    | X5 != X1
    | X4 != X0
    | X6 != X3
    | sK3 != X2 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_3908,plain,
    ( ~ r2_relset_1(X0,X1,sK3,X2)
    | r2_relset_1(X3,X4,sK3,X5)
    | X4 != X1
    | X3 != X0
    | X5 != X2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_5960,plain,
    ( r2_relset_1(X0,X1,sK3,X2)
    | ~ r2_relset_1(X3,X4,sK3,sK3)
    | X0 != X3
    | X1 != X4
    | X2 != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3908])).

cnf(c_13078,plain,
    ( r2_relset_1(X0,X1,sK3,k2_funct_1(sK2))
    | ~ r2_relset_1(X2,X3,sK3,sK3)
    | X0 != X2
    | X1 != X3
    | k2_funct_1(sK2) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5960])).

cnf(c_13080,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2))
    | ~ r2_relset_1(sK1,sK1,sK3,sK3)
    | k2_funct_1(sK2) != sK3
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_13078])).

cnf(c_2680,plain,
    ( ~ r2_relset_1(X0,X1,sK3,X2)
    | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) != X2
    | sK3 != sK3
    | sK1 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2467])).

cnf(c_3000,plain,
    ( ~ r2_relset_1(X0,X1,sK3,k2_funct_1(sK2))
    | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | sK3 != sK3
    | sK1 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_3002,plain,
    ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
    | ~ r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2))
    | k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_2694,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_2491,plain,
    ( r2_relset_1(sK1,sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14024,c_13080,c_3688,c_3002,c_2694,c_2491,c_1617,c_32,c_49,c_34,c_47,c_46,c_38,c_39,c_40,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:02:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.76/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.99  
% 3.76/0.99  ------  iProver source info
% 3.76/0.99  
% 3.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.99  git: non_committed_changes: false
% 3.76/0.99  git: last_make_outside_of_git: false
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    ""
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         true
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     num_symb
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       true
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     true
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_input_bw                          []
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  ------ Parsing...
% 3.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.99  ------ Proving...
% 3.76/0.99  ------ Problem Properties 
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  clauses                                 37
% 3.76/0.99  conjectures                             10
% 3.76/0.99  EPR                                     9
% 3.76/0.99  Horn                                    34
% 3.76/0.99  unary                                   14
% 3.76/0.99  binary                                  7
% 3.76/0.99  lits                                    105
% 3.76/0.99  lits eq                                 14
% 3.76/0.99  fd_pure                                 0
% 3.76/0.99  fd_pseudo                               0
% 3.76/0.99  fd_cond                                 1
% 3.76/0.99  fd_pseudo_cond                          4
% 3.76/0.99  AC symbols                              0
% 3.76/0.99  
% 3.76/0.99  ------ Schedule dynamic 5 is on 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  Current options:
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    ""
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         true
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     none
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       false
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     true
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Simplification Setup
% 3.76/0.99  
% 3.76/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_immed_triv                        [TrivRules]
% 3.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_immed_bw_main                     []
% 3.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/0.99  --sup_input_bw                          []
% 3.76/0.99  
% 3.76/0.99  ------ Combination Options
% 3.76/0.99  
% 3.76/0.99  --comb_res_mult                         3
% 3.76/0.99  --comb_sup_mult                         2
% 3.76/0.99  --comb_inst_mult                        10
% 3.76/0.99  
% 3.76/0.99  ------ Debug Options
% 3.76/0.99  
% 3.76/0.99  --dbg_backtrace                         false
% 3.76/0.99  --dbg_dump_prop_clauses                 false
% 3.76/0.99  --dbg_dump_prop_clauses_file            -
% 3.76/0.99  --dbg_out_stat                          false
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  ------ Proving...
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS status Theorem for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  fof(f20,conjecture,(
% 3.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f21,negated_conjecture,(
% 3.76/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.76/0.99    inference(negated_conjecture,[],[f20])).
% 3.76/0.99  
% 3.76/0.99  fof(f45,plain,(
% 3.76/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f21])).
% 3.76/0.99  
% 3.76/0.99  fof(f46,plain,(
% 3.76/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.76/0.99    inference(flattening,[],[f45])).
% 3.76/0.99  
% 3.76/0.99  fof(f57,plain,(
% 3.76/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK3,X0,X0) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f56,plain,(
% 3.76/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),k6_partfun1(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(X2,sK1,sK1) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.76/0.99    introduced(choice_axiom,[])).
% 3.76/0.99  
% 3.76/0.99  fof(f58,plain,(
% 3.76/0.99    (~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK3,sK1,sK1) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f57,f56])).
% 3.76/0.99  
% 3.76/0.99  fof(f100,plain,(
% 3.76/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1))),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f95,plain,(
% 3.76/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f12,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f31,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(ennf_transformation,[],[f12])).
% 3.76/0.99  
% 3.76/0.99  fof(f32,plain,(
% 3.76/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(flattening,[],[f31])).
% 3.76/0.99  
% 3.76/0.99  fof(f78,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f32])).
% 3.76/0.99  
% 3.76/0.99  fof(f92,plain,(
% 3.76/0.99    v1_funct_1(sK2)),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f94,plain,(
% 3.76/0.99    v3_funct_2(sK2,sK1,sK1)),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f7,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f22,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.76/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.76/0.99  
% 3.76/0.99  fof(f26,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(ennf_transformation,[],[f22])).
% 3.76/0.99  
% 3.76/0.99  fof(f70,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f26])).
% 3.76/0.99  
% 3.76/0.99  fof(f13,axiom,(
% 3.76/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f33,plain,(
% 3.76/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f13])).
% 3.76/0.99  
% 3.76/0.99  fof(f34,plain,(
% 3.76/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.76/0.99    inference(flattening,[],[f33])).
% 3.76/0.99  
% 3.76/0.99  fof(f55,plain,(
% 3.76/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.76/0.99    inference(nnf_transformation,[],[f34])).
% 3.76/0.99  
% 3.76/0.99  fof(f79,plain,(
% 3.76/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f55])).
% 3.76/0.99  
% 3.76/0.99  fof(f6,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f25,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(ennf_transformation,[],[f6])).
% 3.76/0.99  
% 3.76/0.99  fof(f69,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f25])).
% 3.76/0.99  
% 3.76/0.99  fof(f9,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f28,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(ennf_transformation,[],[f9])).
% 3.76/0.99  
% 3.76/0.99  fof(f72,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f28])).
% 3.76/0.99  
% 3.76/0.99  fof(f19,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f43,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.76/0.99    inference(ennf_transformation,[],[f19])).
% 3.76/0.99  
% 3.76/0.99  fof(f44,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.76/0.99    inference(flattening,[],[f43])).
% 3.76/0.99  
% 3.76/0.99  fof(f91,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f44])).
% 3.76/0.99  
% 3.76/0.99  fof(f18,axiom,(
% 3.76/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f41,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.76/0.99    inference(ennf_transformation,[],[f18])).
% 3.76/0.99  
% 3.76/0.99  fof(f42,plain,(
% 3.76/0.99    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.76/0.99    inference(flattening,[],[f41])).
% 3.76/0.99  
% 3.76/0.99  fof(f89,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f42])).
% 3.76/0.99  
% 3.76/0.99  fof(f2,axiom,(
% 3.76/0.99    v1_xboole_0(k1_xboole_0)),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f62,plain,(
% 3.76/0.99    v1_xboole_0(k1_xboole_0)),
% 3.76/0.99    inference(cnf_transformation,[],[f2])).
% 3.76/0.99  
% 3.76/0.99  fof(f93,plain,(
% 3.76/0.99    v1_funct_2(sK2,sK1,sK1)),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f16,axiom,(
% 3.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f39,plain,(
% 3.76/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f16])).
% 3.76/0.99  
% 3.76/0.99  fof(f40,plain,(
% 3.76/0.99    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.76/0.99    inference(flattening,[],[f39])).
% 3.76/0.99  
% 3.76/0.99  fof(f87,plain,(
% 3.76/0.99    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f40])).
% 3.76/0.99  
% 3.76/0.99  fof(f15,axiom,(
% 3.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f37,plain,(
% 3.76/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.76/0.99    inference(ennf_transformation,[],[f15])).
% 3.76/0.99  
% 3.76/0.99  fof(f38,plain,(
% 3.76/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.76/0.99    inference(flattening,[],[f37])).
% 3.76/0.99  
% 3.76/0.99  fof(f86,plain,(
% 3.76/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f38])).
% 3.76/0.99  
% 3.76/0.99  fof(f8,axiom,(
% 3.76/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f27,plain,(
% 3.76/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.76/0.99    inference(ennf_transformation,[],[f8])).
% 3.76/0.99  
% 3.76/0.99  fof(f71,plain,(
% 3.76/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f27])).
% 3.76/0.99  
% 3.76/0.99  fof(f101,plain,(
% 3.76/0.99    ~r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f11,axiom,(
% 3.76/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f75,plain,(
% 3.76/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f11])).
% 3.76/0.99  
% 3.76/0.99  fof(f17,axiom,(
% 3.76/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f88,plain,(
% 3.76/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f17])).
% 3.76/0.99  
% 3.76/0.99  fof(f102,plain,(
% 3.76/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.76/0.99    inference(definition_unfolding,[],[f75,f88])).
% 3.76/0.99  
% 3.76/0.99  fof(f10,axiom,(
% 3.76/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f29,plain,(
% 3.76/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.76/0.99    inference(ennf_transformation,[],[f10])).
% 3.76/0.99  
% 3.76/0.99  fof(f30,plain,(
% 3.76/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(flattening,[],[f29])).
% 3.76/0.99  
% 3.76/0.99  fof(f54,plain,(
% 3.76/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.99    inference(nnf_transformation,[],[f30])).
% 3.76/0.99  
% 3.76/0.99  fof(f74,plain,(
% 3.76/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(cnf_transformation,[],[f54])).
% 3.76/0.99  
% 3.76/0.99  fof(f105,plain,(
% 3.76/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.99    inference(equality_resolution,[],[f74])).
% 3.76/0.99  
% 3.76/0.99  fof(f3,axiom,(
% 3.76/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.99  
% 3.76/0.99  fof(f24,plain,(
% 3.76/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.76/0.99    inference(ennf_transformation,[],[f3])).
% 3.76/0.99  
% 3.76/0.99  fof(f63,plain,(
% 3.76/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.76/0.99    inference(cnf_transformation,[],[f24])).
% 3.76/0.99  
% 3.76/0.99  fof(f99,plain,(
% 3.76/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f97,plain,(
% 3.76/0.99    v1_funct_2(sK3,sK1,sK1)),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  fof(f96,plain,(
% 3.76/0.99    v1_funct_1(sK3)),
% 3.76/0.99    inference(cnf_transformation,[],[f58])).
% 3.76/0.99  
% 3.76/0.99  cnf(c_33,negated_conjecture,
% 3.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2400,plain,
% 3.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),k6_partfun1(sK1)) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_38,negated_conjecture,
% 3.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.76/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2395,plain,
% 3.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_17,plain,
% 3.76/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.76/0.99      | v2_funct_2(X0,X2)
% 3.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.99      | ~ v1_funct_1(X0) ),
% 3.76/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2410,plain,
% 3.76/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.76/1.00      | v2_funct_2(X0,X2) = iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6052,plain,
% 3.76/1.00      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | v2_funct_2(sK2,sK1) = iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2395,c_2410]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_41,negated_conjecture,
% 3.76/1.00      ( v1_funct_1(sK2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_42,plain,
% 3.76/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_39,negated_conjecture,
% 3.76/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_44,plain,
% 3.76/1.00      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6396,plain,
% 3.76/1.00      ( v2_funct_2(sK2,sK1) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_6052,c_42,c_44]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11,plain,
% 3.76/1.00      ( v5_relat_1(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_21,plain,
% 3.76/1.00      ( ~ v2_funct_2(X0,X1)
% 3.76/1.00      | ~ v5_relat_1(X0,X1)
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k2_relat_1(X0) = X1 ),
% 3.76/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_546,plain,
% 3.76/1.00      ( ~ v2_funct_2(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.76/1.00      | ~ v1_relat_1(X0)
% 3.76/1.00      | k2_relat_1(X0) = X1 ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_11,c_21]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_558,plain,
% 3.76/1.00      ( ~ v2_funct_2(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.76/1.00      | k2_relat_1(X0) = X1 ),
% 3.76/1.00      inference(forward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_546,c_10]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2390,plain,
% 3.76/1.00      ( k2_relat_1(X0) = X1
% 3.76/1.00      | v2_funct_2(X0,X1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4175,plain,
% 3.76/1.00      ( k2_relat_1(sK2) = sK1 | v2_funct_2(sK2,sK1) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2395,c_2390]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6400,plain,
% 3.76/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_6396,c_4175]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2414,plain,
% 3.76/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4433,plain,
% 3.76/1.00      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2395,c_2414]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_6470,plain,
% 3.76/1.00      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.76/1.00      inference(demodulation,[status(thm)],[c_6400,c_4433]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_31,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.76/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.76/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.76/1.00      | ~ v2_funct_1(X2)
% 3.76/1.00      | ~ v1_funct_1(X2)
% 3.76/1.00      | ~ v1_funct_1(X3)
% 3.76/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.76/1.00      | k2_funct_1(X2) = X3
% 3.76/1.00      | k1_xboole_0 = X1
% 3.76/1.00      | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_30,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.76/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.76/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.76/1.00      | v2_funct_1(X2)
% 3.76/1.00      | ~ v1_funct_1(X2)
% 3.76/1.00      | ~ v1_funct_1(X3) ),
% 3.76/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_223,plain,
% 3.76/1.00      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.76/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.76/1.00      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.76/1.00      | ~ v1_funct_1(X2)
% 3.76/1.00      | ~ v1_funct_1(X3)
% 3.76/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.76/1.00      | k2_funct_1(X2) = X3
% 3.76/1.00      | k1_xboole_0 = X1
% 3.76/1.00      | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_31,c_30]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_224,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.76/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.76/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.76/1.00      | ~ v1_funct_1(X3)
% 3.76/1.00      | ~ v1_funct_1(X2)
% 3.76/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.76/1.00      | k2_funct_1(X2) = X3
% 3.76/1.00      | k1_xboole_0 = X1
% 3.76/1.00      | k1_xboole_0 = X0 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_223]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2391,plain,
% 3.76/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.76/1.00      | k2_funct_1(X2) = X3
% 3.76/1.00      | k1_xboole_0 = X1
% 3.76/1.00      | k1_xboole_0 = X0
% 3.76/1.00      | r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 3.76/1.00      | v1_funct_2(X3,X1,X0) != iProver_top
% 3.76/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.76/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.76/1.00      | v1_funct_1(X2) != iProver_top
% 3.76/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7175,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = X0
% 3.76/1.00      | sK1 = k1_xboole_0
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_6470,c_2391]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3,plain,
% 3.76/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_126,plain,
% 3.76/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1591,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2939,plain,
% 3.76/1.00      ( v1_xboole_0(X0)
% 3.76/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.76/1.00      | X0 != k1_xboole_0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2940,plain,
% 3.76/1.00      ( X0 != k1_xboole_0
% 3.76/1.00      | v1_xboole_0(X0) = iProver_top
% 3.76/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2939]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2942,plain,
% 3.76/1.00      ( sK1 != k1_xboole_0
% 3.76/1.00      | v1_xboole_0(sK1) = iProver_top
% 3.76/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2940]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5097,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = X0
% 3.76/1.00      | k2_relat_1(sK2) != sK1
% 3.76/1.00      | sK1 = k1_xboole_0
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_4433,c_2391]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_40,negated_conjecture,
% 3.76/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_43,plain,
% 3.76/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_45,plain,
% 3.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5438,plain,
% 3.76/1.00      ( v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | sK1 = k1_xboole_0
% 3.76/1.00      | k2_relat_1(sK2) != sK1
% 3.76/1.00      | k2_funct_1(sK2) = X0
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_5097,c_42,c_43,c_45]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5439,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = X0
% 3.76/1.00      | k2_relat_1(sK2) != sK1
% 3.76/1.00      | sK1 = k1_xboole_0
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_5438]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_28,plain,
% 3.76/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.76/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2403,plain,
% 3.76/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.76/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.76/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.76/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.76/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7391,plain,
% 3.76/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.76/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2395,c_2403]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3688,plain,
% 3.76/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.76/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.76/1.00      | ~ v1_funct_1(sK2)
% 3.76/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7655,plain,
% 3.76/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_7391,c_41,c_40,c_39,c_38,c_3688]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_24,plain,
% 3.76/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.76/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.76/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.76/1.00      | ~ v1_funct_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2407,plain,
% 3.76/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.76/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.76/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8350,plain,
% 3.76/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.76/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_7655,c_2407]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9051,plain,
% 3.76/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_8350,c_42,c_43,c_44,c_45]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | ~ v1_xboole_0(X1)
% 3.76/1.00      | v1_xboole_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2415,plain,
% 3.76/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.76/1.00      | v1_xboole_0(X1) != iProver_top
% 3.76/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9057,plain,
% 3.76/1.00      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_9051,c_2415]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_32,negated_conjecture,
% 3.76/1.00      ( ~ r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_96,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_95,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_97,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_95]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1588,plain,( X0 = X0 ),theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1617,plain,
% 3.76/1.00      ( sK1 = sK1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1595,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.76/1.00      | r2_relset_1(X4,X5,X6,X7)
% 3.76/1.00      | X5 != X1
% 3.76/1.00      | X4 != X0
% 3.76/1.00      | X6 != X2
% 3.76/1.00      | X7 != X3 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2467,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.76/1.00      | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.76/1.00      | k2_funct_2(sK1,sK2) != X3
% 3.76/1.00      | sK3 != X2
% 3.76/1.00      | sK1 != X1
% 3.76/1.00      | sK1 != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2469,plain,
% 3.76/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.76/1.00      | ~ r2_relset_1(sK1,sK1,sK1,sK1)
% 3.76/1.00      | k2_funct_2(sK1,sK2) != sK1
% 3.76/1.00      | sK3 != sK1
% 3.76/1.00      | sK1 != sK1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2467]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,plain,
% 3.76/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2502,plain,
% 3.76/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.76/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2504,plain,
% 3.76/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 3.76/1.00      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2502]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2542,plain,
% 3.76/1.00      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/1.00      | ~ v1_xboole_0(X0)
% 3.76/1.00      | v1_xboole_0(k6_partfun1(sK1)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2543,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/1.00      | v1_xboole_0(X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(k6_partfun1(sK1)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2542]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2545,plain,
% 3.76/1.00      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2543]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2620,plain,
% 3.76/1.00      ( r2_relset_1(X0,X1,X2,X3)
% 3.76/1.00      | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X4))
% 3.76/1.00      | X1 != X4
% 3.76/1.00      | X0 != X4
% 3.76/1.00      | X2 != k6_partfun1(X4)
% 3.76/1.00      | X3 != k6_partfun1(X4) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2622,plain,
% 3.76/1.00      ( ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 3.76/1.00      | r2_relset_1(sK1,sK1,sK1,sK1)
% 3.76/1.00      | sK1 != k6_partfun1(sK1)
% 3.76/1.00      | sK1 != sK1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2620]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.76/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2670,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2671,plain,
% 3.76/1.00      ( sK3 = X0
% 3.76/1.00      | v1_xboole_0(X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_2670]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2673,plain,
% 3.76/1.00      ( sK3 = sK1
% 3.76/1.00      | v1_xboole_0(sK3) != iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2671]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3278,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0)
% 3.76/1.00      | ~ v1_xboole_0(k6_partfun1(sK1))
% 3.76/1.00      | X0 = k6_partfun1(sK1) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3279,plain,
% 3.76/1.00      ( X0 = k6_partfun1(sK1)
% 3.76/1.00      | v1_xboole_0(X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(k6_partfun1(sK1)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3278]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3281,plain,
% 3.76/1.00      ( sK1 = k6_partfun1(sK1)
% 3.76/1.00      | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3279]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1589,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3008,plain,
% 3.76/1.00      ( X0 != X1 | k2_funct_2(sK1,sK2) != X1 | k2_funct_2(sK1,sK2) = X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3699,plain,
% 3.76/1.00      ( X0 != k2_funct_1(sK2)
% 3.76/1.00      | k2_funct_2(sK1,sK2) = X0
% 3.76/1.00      | k2_funct_2(sK1,sK2) != k2_funct_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3008]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3700,plain,
% 3.76/1.00      ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 3.76/1.00      | k2_funct_2(sK1,sK2) = sK1
% 3.76/1.00      | sK1 != k2_funct_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3699]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5601,plain,
% 3.76/1.00      ( ~ v1_xboole_0(X0)
% 3.76/1.00      | ~ v1_xboole_0(k2_funct_1(sK2))
% 3.76/1.00      | X0 = k2_funct_1(sK2) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5602,plain,
% 3.76/1.00      ( X0 = k2_funct_1(sK2)
% 3.76/1.00      | v1_xboole_0(X0) != iProver_top
% 3.76/1.00      | v1_xboole_0(k2_funct_1(sK2)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_5601]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5604,plain,
% 3.76/1.00      ( sK1 = k2_funct_1(sK2)
% 3.76/1.00      | v1_xboole_0(k2_funct_1(sK2)) != iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_5602]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_34,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2399,plain,
% 3.76/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5883,plain,
% 3.76/1.00      ( v1_xboole_0(sK3) = iProver_top
% 3.76/1.00      | v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2399,c_2415]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10586,plain,
% 3.76/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_9057,c_41,c_40,c_39,c_38,c_32,c_96,c_97,c_1617,c_2469,
% 3.76/1.00                 c_2504,c_2545,c_2622,c_2673,c_3281,c_3688,c_3700,c_5604,
% 3.76/1.00                 c_5883]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14018,plain,
% 3.76/1.00      ( v1_funct_1(X0) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | k2_funct_1(sK2) = X0
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_7175,c_41,c_42,c_40,c_43,c_39,c_44,c_38,c_45,c_32,
% 3.76/1.00                 c_96,c_97,c_126,c_1617,c_2469,c_2504,c_2545,c_2622,
% 3.76/1.00                 c_2673,c_2942,c_3281,c_3688,c_3700,c_4175,c_5097,c_5604,
% 3.76/1.00                 c_5883,c_6052,c_9057]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14019,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = X0
% 3.76/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X0),k6_partfun1(sK1)) != iProver_top
% 3.76/1.00      | v1_funct_2(X0,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_14018]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14024,plain,
% 3.76/1.00      ( k2_funct_1(sK2) = sK3
% 3.76/1.00      | v1_funct_2(sK3,sK1,sK1) != iProver_top
% 3.76/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.76/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_2400,c_14019]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3170,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.76/1.00      | r2_relset_1(X4,X5,sK3,X6)
% 3.76/1.00      | X5 != X1
% 3.76/1.00      | X4 != X0
% 3.76/1.00      | X6 != X3
% 3.76/1.00      | sK3 != X2 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3908,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,sK3,X2)
% 3.76/1.00      | r2_relset_1(X3,X4,sK3,X5)
% 3.76/1.00      | X4 != X1
% 3.76/1.00      | X3 != X0
% 3.76/1.00      | X5 != X2
% 3.76/1.00      | sK3 != sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3170]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5960,plain,
% 3.76/1.00      ( r2_relset_1(X0,X1,sK3,X2)
% 3.76/1.00      | ~ r2_relset_1(X3,X4,sK3,sK3)
% 3.76/1.00      | X0 != X3
% 3.76/1.00      | X1 != X4
% 3.76/1.00      | X2 != sK3
% 3.76/1.00      | sK3 != sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3908]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13078,plain,
% 3.76/1.00      ( r2_relset_1(X0,X1,sK3,k2_funct_1(sK2))
% 3.76/1.00      | ~ r2_relset_1(X2,X3,sK3,sK3)
% 3.76/1.00      | X0 != X2
% 3.76/1.00      | X1 != X3
% 3.76/1.00      | k2_funct_1(sK2) != sK3
% 3.76/1.00      | sK3 != sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_5960]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13080,plain,
% 3.76/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2))
% 3.76/1.00      | ~ r2_relset_1(sK1,sK1,sK3,sK3)
% 3.76/1.00      | k2_funct_1(sK2) != sK3
% 3.76/1.00      | sK3 != sK3
% 3.76/1.00      | sK1 != sK1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_13078]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2680,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,sK3,X2)
% 3.76/1.00      | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.76/1.00      | k2_funct_2(sK1,sK2) != X2
% 3.76/1.00      | sK3 != sK3
% 3.76/1.00      | sK1 != X1
% 3.76/1.00      | sK1 != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2467]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3000,plain,
% 3.76/1.00      ( ~ r2_relset_1(X0,X1,sK3,k2_funct_1(sK2))
% 3.76/1.00      | r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.76/1.00      | k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 3.76/1.00      | sK3 != sK3
% 3.76/1.00      | sK1 != X1
% 3.76/1.00      | sK1 != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2680]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3002,plain,
% 3.76/1.00      ( r2_relset_1(sK1,sK1,sK3,k2_funct_2(sK1,sK2))
% 3.76/1.00      | ~ r2_relset_1(sK1,sK1,sK3,k2_funct_1(sK2))
% 3.76/1.00      | k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 3.76/1.00      | sK3 != sK3
% 3.76/1.00      | sK1 != sK1 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3000]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2694,plain,
% 3.76/1.00      ( sK3 = sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1588]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2491,plain,
% 3.76/1.00      ( r2_relset_1(sK1,sK1,sK3,sK3)
% 3.76/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_49,plain,
% 3.76/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_36,negated_conjecture,
% 3.76/1.00      ( v1_funct_2(sK3,sK1,sK1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_47,plain,
% 3.76/1.00      ( v1_funct_2(sK3,sK1,sK1) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_37,negated_conjecture,
% 3.76/1.00      ( v1_funct_1(sK3) ),
% 3.76/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_46,plain,
% 3.76/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(contradiction,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(minisat,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_14024,c_13080,c_3688,c_3002,c_2694,c_2491,c_1617,c_32,
% 3.76/1.00                 c_49,c_34,c_47,c_46,c_38,c_39,c_40,c_41]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ General
% 3.76/1.00  
% 3.76/1.00  abstr_ref_over_cycles:                  0
% 3.76/1.00  abstr_ref_under_cycles:                 0
% 3.76/1.00  gc_basic_clause_elim:                   0
% 3.76/1.00  forced_gc_time:                         0
% 3.76/1.00  parsing_time:                           0.01
% 3.76/1.00  unif_index_cands_time:                  0.
% 3.76/1.00  unif_index_add_time:                    0.
% 3.76/1.00  orderings_time:                         0.
% 3.76/1.00  out_proof_time:                         0.014
% 3.76/1.00  total_time:                             0.444
% 3.76/1.00  num_of_symbols:                         56
% 3.76/1.00  num_of_terms:                           15322
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing
% 3.76/1.00  
% 3.76/1.00  num_of_splits:                          0
% 3.76/1.00  num_of_split_atoms:                     0
% 3.76/1.00  num_of_reused_defs:                     0
% 3.76/1.00  num_eq_ax_congr_red:                    36
% 3.76/1.00  num_of_sem_filtered_clauses:            3
% 3.76/1.00  num_of_subtypes:                        0
% 3.76/1.00  monotx_restored_types:                  0
% 3.76/1.00  sat_num_of_epr_types:                   0
% 3.76/1.00  sat_num_of_non_cyclic_types:            0
% 3.76/1.00  sat_guarded_non_collapsed_types:        0
% 3.76/1.00  num_pure_diseq_elim:                    0
% 3.76/1.00  simp_replaced_by:                       0
% 3.76/1.00  res_preprocessed:                       183
% 3.76/1.00  prep_upred:                             0
% 3.76/1.00  prep_unflattend:                        64
% 3.76/1.00  smt_new_axioms:                         0
% 3.76/1.00  pred_elim_cands:                        9
% 3.76/1.00  pred_elim:                              2
% 3.76/1.00  pred_elim_cl:                           2
% 3.76/1.00  pred_elim_cycles:                       9
% 3.76/1.00  merged_defs:                            8
% 3.76/1.00  merged_defs_ncl:                        0
% 3.76/1.00  bin_hyper_res:                          8
% 3.76/1.00  prep_cycles:                            4
% 3.76/1.00  pred_elim_time:                         0.018
% 3.76/1.00  splitting_time:                         0.
% 3.76/1.00  sem_filter_time:                        0.
% 3.76/1.00  monotx_time:                            0.001
% 3.76/1.00  subtype_inf_time:                       0.
% 3.76/1.00  
% 3.76/1.00  ------ Problem properties
% 3.76/1.00  
% 3.76/1.00  clauses:                                37
% 3.76/1.00  conjectures:                            10
% 3.76/1.00  epr:                                    9
% 3.76/1.00  horn:                                   34
% 3.76/1.00  ground:                                 11
% 3.76/1.00  unary:                                  14
% 3.76/1.00  binary:                                 7
% 3.76/1.00  lits:                                   105
% 3.76/1.00  lits_eq:                                14
% 3.76/1.00  fd_pure:                                0
% 3.76/1.00  fd_pseudo:                              0
% 3.76/1.00  fd_cond:                                1
% 3.76/1.00  fd_pseudo_cond:                         4
% 3.76/1.00  ac_symbols:                             0
% 3.76/1.00  
% 3.76/1.00  ------ Propositional Solver
% 3.76/1.00  
% 3.76/1.00  prop_solver_calls:                      29
% 3.76/1.00  prop_fast_solver_calls:                 1806
% 3.76/1.00  smt_solver_calls:                       0
% 3.76/1.00  smt_fast_solver_calls:                  0
% 3.76/1.00  prop_num_of_clauses:                    5505
% 3.76/1.00  prop_preprocess_simplified:             12187
% 3.76/1.00  prop_fo_subsumed:                       94
% 3.76/1.00  prop_solver_time:                       0.
% 3.76/1.00  smt_solver_time:                        0.
% 3.76/1.00  smt_fast_solver_time:                   0.
% 3.76/1.00  prop_fast_solver_time:                  0.
% 3.76/1.00  prop_unsat_core_time:                   0.
% 3.76/1.00  
% 3.76/1.00  ------ QBF
% 3.76/1.00  
% 3.76/1.00  qbf_q_res:                              0
% 3.76/1.00  qbf_num_tautologies:                    0
% 3.76/1.00  qbf_prep_cycles:                        0
% 3.76/1.00  
% 3.76/1.00  ------ BMC1
% 3.76/1.00  
% 3.76/1.00  bmc1_current_bound:                     -1
% 3.76/1.00  bmc1_last_solved_bound:                 -1
% 3.76/1.00  bmc1_unsat_core_size:                   -1
% 3.76/1.00  bmc1_unsat_core_parents_size:           -1
% 3.76/1.00  bmc1_merge_next_fun:                    0
% 3.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation
% 3.76/1.00  
% 3.76/1.00  inst_num_of_clauses:                    1492
% 3.76/1.00  inst_num_in_passive:                    163
% 3.76/1.00  inst_num_in_active:                     667
% 3.76/1.00  inst_num_in_unprocessed:                662
% 3.76/1.00  inst_num_of_loops:                      790
% 3.76/1.00  inst_num_of_learning_restarts:          0
% 3.76/1.00  inst_num_moves_active_passive:          119
% 3.76/1.00  inst_lit_activity:                      0
% 3.76/1.00  inst_lit_activity_moves:                0
% 3.76/1.00  inst_num_tautologies:                   0
% 3.76/1.00  inst_num_prop_implied:                  0
% 3.76/1.00  inst_num_existing_simplified:           0
% 3.76/1.00  inst_num_eq_res_simplified:             0
% 3.76/1.00  inst_num_child_elim:                    0
% 3.76/1.00  inst_num_of_dismatching_blockings:      1307
% 3.76/1.00  inst_num_of_non_proper_insts:           2537
% 3.76/1.00  inst_num_of_duplicates:                 0
% 3.76/1.00  inst_inst_num_from_inst_to_res:         0
% 3.76/1.00  inst_dismatching_checking_time:         0.
% 3.76/1.00  
% 3.76/1.00  ------ Resolution
% 3.76/1.00  
% 3.76/1.00  res_num_of_clauses:                     0
% 3.76/1.00  res_num_in_passive:                     0
% 3.76/1.00  res_num_in_active:                      0
% 3.76/1.00  res_num_of_loops:                       187
% 3.76/1.00  res_forward_subset_subsumed:            151
% 3.76/1.00  res_backward_subset_subsumed:           0
% 3.76/1.00  res_forward_subsumed:                   0
% 3.76/1.00  res_backward_subsumed:                  0
% 3.76/1.00  res_forward_subsumption_resolution:     4
% 3.76/1.00  res_backward_subsumption_resolution:    0
% 3.76/1.00  res_clause_to_clause_subsumption:       660
% 3.76/1.00  res_orphan_elimination:                 0
% 3.76/1.00  res_tautology_del:                      183
% 3.76/1.00  res_num_eq_res_simplified:              0
% 3.76/1.00  res_num_sel_changes:                    0
% 3.76/1.00  res_moves_from_active_to_pass:          0
% 3.76/1.00  
% 3.76/1.00  ------ Superposition
% 3.76/1.00  
% 3.76/1.00  sup_time_total:                         0.
% 3.76/1.00  sup_time_generating:                    0.
% 3.76/1.00  sup_time_sim_full:                      0.
% 3.76/1.00  sup_time_sim_immed:                     0.
% 3.76/1.00  
% 3.76/1.00  sup_num_of_clauses:                     248
% 3.76/1.00  sup_num_in_active:                      142
% 3.76/1.00  sup_num_in_passive:                     106
% 3.76/1.00  sup_num_of_loops:                       157
% 3.76/1.00  sup_fw_superposition:                   171
% 3.76/1.00  sup_bw_superposition:                   117
% 3.76/1.00  sup_immediate_simplified:               32
% 3.76/1.00  sup_given_eliminated:                   1
% 3.76/1.00  comparisons_done:                       0
% 3.76/1.00  comparisons_avoided:                    0
% 3.76/1.00  
% 3.76/1.00  ------ Simplifications
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  sim_fw_subset_subsumed:                 7
% 3.76/1.00  sim_bw_subset_subsumed:                 8
% 3.76/1.00  sim_fw_subsumed:                        8
% 3.76/1.00  sim_bw_subsumed:                        3
% 3.76/1.00  sim_fw_subsumption_res:                 0
% 3.76/1.00  sim_bw_subsumption_res:                 0
% 3.76/1.00  sim_tautology_del:                      1
% 3.76/1.00  sim_eq_tautology_del:                   14
% 3.76/1.00  sim_eq_res_simp:                        2
% 3.76/1.00  sim_fw_demodulated:                     13
% 3.76/1.00  sim_bw_demodulated:                     12
% 3.76/1.00  sim_light_normalised:                   16
% 3.76/1.00  sim_joinable_taut:                      0
% 3.76/1.00  sim_joinable_simp:                      0
% 3.76/1.00  sim_ac_normalised:                      0
% 3.76/1.00  sim_smt_subsumption:                    0
% 3.76/1.00  
%------------------------------------------------------------------------------
