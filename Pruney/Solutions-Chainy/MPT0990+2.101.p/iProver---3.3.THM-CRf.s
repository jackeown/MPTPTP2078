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
% DateTime   : Thu Dec  3 12:03:18 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 800 expanded)
%              Number of clauses        :  131 ( 234 expanded)
%              Number of leaves         :   24 ( 201 expanded)
%              Depth                    :   24
%              Number of atoms          :  875 (6584 expanded)
%              Number of equality atoms :  417 (2396 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f24])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f66,f65])).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f107,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f114,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f117,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f101])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f80,f101,f101])).

fof(f125,plain,(
    ! [X2,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1))
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f121])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f116,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f67])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f118,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2431,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2434,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2441,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10250,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2441])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_53,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_10614,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10250,c_53])).

cnf(c_10615,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10614])).

cnf(c_10626,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_10615])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3051,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3560,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3051])).

cnf(c_4212,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_5833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4212])).

cnf(c_10786,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10626,c_49,c_47,c_46,c_44,c_5833])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
    | k6_partfun1(sK0) != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_42])).

cnf(c_514,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_522,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_514,c_31])).

cnf(c_2427,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_10789,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10786,c_2427])).

cnf(c_52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2449,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9253,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2449])).

cnf(c_9757,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2431,c_9253])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2452,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9856,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9757,c_2452])).

cnf(c_11727,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10789,c_52,c_55,c_9856])).

cnf(c_43,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2437,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5689,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_43,c_2437])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_41,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3064,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3535,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3064])).

cnf(c_4024,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3535])).

cnf(c_6202,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5689,c_49,c_48,c_47,c_43,c_41,c_39,c_4024])).

cnf(c_2435,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2456,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5968,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2435,c_2456])).

cnf(c_928,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_41])).

cnf(c_929,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2842,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3454,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3966,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6369,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5968,c_49,c_47,c_929,c_3454,c_3966])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2436,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4481,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_43,c_2436])).

cnf(c_3074,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_3545,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3074])).

cnf(c_4027,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3545])).

cnf(c_4749,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4481,c_49,c_48,c_47,c_43,c_41,c_39,c_4027])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2461,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4752,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4749,c_2461])).

cnf(c_8,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4753,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4752,c_8])).

cnf(c_50,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2831,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2832,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_3455,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3454])).

cnf(c_3967,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3966])).

cnf(c_4990,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4753,c_50,c_52,c_2832,c_3455,c_3967])).

cnf(c_6373,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6369,c_4990])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_5])).

cnf(c_2428,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_3518,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2428])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2465,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4180,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_2465])).

cnf(c_4296,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
    | k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4180,c_52,c_3455,c_3967])).

cnf(c_4297,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4296])).

cnf(c_6389,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_6373,c_4297])).

cnf(c_7629,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_6389,c_6369])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2))
    | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2458,plain,
    ( X0 = X1
    | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10325,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7629,c_2458])).

cnf(c_51,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_57,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3012,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3419,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_3420,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3419])).

cnf(c_49821,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10325,c_50,c_51,c_52,c_43,c_57,c_2832,c_3420,c_3455,c_3967])).

cnf(c_49822,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_49821])).

cnf(c_49834,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6202,c_49822])).

cnf(c_50006,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49834,c_50,c_52,c_3455,c_3967])).

cnf(c_50007,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_50006])).

cnf(c_50018,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11727,c_50007])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2443,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6969,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2443])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2451,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3579,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2434,c_2451])).

cnf(c_6978,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6969,c_3579])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_54,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_40,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_158,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_162,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1762,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2913,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2914,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2913])).

cnf(c_7386,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6978,c_54,c_40,c_158,c_162,c_2914])).

cnf(c_50023,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_50018,c_7386])).

cnf(c_50024,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_50023])).

cnf(c_3954,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3955,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_3451,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_3452,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3451])).

cnf(c_38,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f118])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50024,c_3955,c_3452,c_38,c_55,c_53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:12:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.65/2.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/2.04  
% 11.65/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.04  
% 11.65/2.04  ------  iProver source info
% 11.65/2.04  
% 11.65/2.04  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.04  git: non_committed_changes: false
% 11.65/2.04  git: last_make_outside_of_git: false
% 11.65/2.04  
% 11.65/2.04  ------ 
% 11.65/2.04  
% 11.65/2.04  ------ Input Options
% 11.65/2.04  
% 11.65/2.04  --out_options                           all
% 11.65/2.04  --tptp_safe_out                         true
% 11.65/2.04  --problem_path                          ""
% 11.65/2.04  --include_path                          ""
% 11.65/2.04  --clausifier                            res/vclausify_rel
% 11.65/2.04  --clausifier_options                    --mode clausify
% 11.65/2.04  --stdin                                 false
% 11.65/2.04  --stats_out                             all
% 11.65/2.04  
% 11.65/2.04  ------ General Options
% 11.65/2.04  
% 11.65/2.04  --fof                                   false
% 11.65/2.04  --time_out_real                         305.
% 11.65/2.04  --time_out_virtual                      -1.
% 11.65/2.04  --symbol_type_check                     false
% 11.65/2.04  --clausify_out                          false
% 11.65/2.04  --sig_cnt_out                           false
% 11.65/2.04  --trig_cnt_out                          false
% 11.65/2.04  --trig_cnt_out_tolerance                1.
% 11.65/2.04  --trig_cnt_out_sk_spl                   false
% 11.65/2.04  --abstr_cl_out                          false
% 11.65/2.04  
% 11.65/2.04  ------ Global Options
% 11.65/2.04  
% 11.65/2.04  --schedule                              default
% 11.65/2.04  --add_important_lit                     false
% 11.65/2.04  --prop_solver_per_cl                    1000
% 11.65/2.04  --min_unsat_core                        false
% 11.65/2.04  --soft_assumptions                      false
% 11.65/2.04  --soft_lemma_size                       3
% 11.65/2.04  --prop_impl_unit_size                   0
% 11.65/2.04  --prop_impl_unit                        []
% 11.65/2.04  --share_sel_clauses                     true
% 11.65/2.04  --reset_solvers                         false
% 11.65/2.04  --bc_imp_inh                            [conj_cone]
% 11.65/2.04  --conj_cone_tolerance                   3.
% 11.65/2.04  --extra_neg_conj                        none
% 11.65/2.04  --large_theory_mode                     true
% 11.65/2.04  --prolific_symb_bound                   200
% 11.65/2.04  --lt_threshold                          2000
% 11.65/2.04  --clause_weak_htbl                      true
% 11.65/2.04  --gc_record_bc_elim                     false
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing Options
% 11.65/2.04  
% 11.65/2.04  --preprocessing_flag                    true
% 11.65/2.04  --time_out_prep_mult                    0.1
% 11.65/2.04  --splitting_mode                        input
% 11.65/2.04  --splitting_grd                         true
% 11.65/2.04  --splitting_cvd                         false
% 11.65/2.04  --splitting_cvd_svl                     false
% 11.65/2.04  --splitting_nvd                         32
% 11.65/2.04  --sub_typing                            true
% 11.65/2.04  --prep_gs_sim                           true
% 11.65/2.04  --prep_unflatten                        true
% 11.65/2.04  --prep_res_sim                          true
% 11.65/2.04  --prep_upred                            true
% 11.65/2.04  --prep_sem_filter                       exhaustive
% 11.65/2.04  --prep_sem_filter_out                   false
% 11.65/2.04  --pred_elim                             true
% 11.65/2.04  --res_sim_input                         true
% 11.65/2.04  --eq_ax_congr_red                       true
% 11.65/2.04  --pure_diseq_elim                       true
% 11.65/2.04  --brand_transform                       false
% 11.65/2.04  --non_eq_to_eq                          false
% 11.65/2.04  --prep_def_merge                        true
% 11.65/2.04  --prep_def_merge_prop_impl              false
% 11.65/2.04  --prep_def_merge_mbd                    true
% 11.65/2.04  --prep_def_merge_tr_red                 false
% 11.65/2.04  --prep_def_merge_tr_cl                  false
% 11.65/2.04  --smt_preprocessing                     true
% 11.65/2.04  --smt_ac_axioms                         fast
% 11.65/2.04  --preprocessed_out                      false
% 11.65/2.04  --preprocessed_stats                    false
% 11.65/2.04  
% 11.65/2.04  ------ Abstraction refinement Options
% 11.65/2.04  
% 11.65/2.04  --abstr_ref                             []
% 11.65/2.04  --abstr_ref_prep                        false
% 11.65/2.04  --abstr_ref_until_sat                   false
% 11.65/2.04  --abstr_ref_sig_restrict                funpre
% 11.65/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.04  --abstr_ref_under                       []
% 11.65/2.04  
% 11.65/2.04  ------ SAT Options
% 11.65/2.04  
% 11.65/2.04  --sat_mode                              false
% 11.65/2.04  --sat_fm_restart_options                ""
% 11.65/2.04  --sat_gr_def                            false
% 11.65/2.04  --sat_epr_types                         true
% 11.65/2.04  --sat_non_cyclic_types                  false
% 11.65/2.04  --sat_finite_models                     false
% 11.65/2.04  --sat_fm_lemmas                         false
% 11.65/2.04  --sat_fm_prep                           false
% 11.65/2.04  --sat_fm_uc_incr                        true
% 11.65/2.04  --sat_out_model                         small
% 11.65/2.04  --sat_out_clauses                       false
% 11.65/2.04  
% 11.65/2.04  ------ QBF Options
% 11.65/2.04  
% 11.65/2.04  --qbf_mode                              false
% 11.65/2.04  --qbf_elim_univ                         false
% 11.65/2.04  --qbf_dom_inst                          none
% 11.65/2.04  --qbf_dom_pre_inst                      false
% 11.65/2.04  --qbf_sk_in                             false
% 11.65/2.04  --qbf_pred_elim                         true
% 11.65/2.04  --qbf_split                             512
% 11.65/2.04  
% 11.65/2.04  ------ BMC1 Options
% 11.65/2.04  
% 11.65/2.04  --bmc1_incremental                      false
% 11.65/2.04  --bmc1_axioms                           reachable_all
% 11.65/2.04  --bmc1_min_bound                        0
% 11.65/2.04  --bmc1_max_bound                        -1
% 11.65/2.04  --bmc1_max_bound_default                -1
% 11.65/2.04  --bmc1_symbol_reachability              true
% 11.65/2.04  --bmc1_property_lemmas                  false
% 11.65/2.04  --bmc1_k_induction                      false
% 11.65/2.04  --bmc1_non_equiv_states                 false
% 11.65/2.04  --bmc1_deadlock                         false
% 11.65/2.04  --bmc1_ucm                              false
% 11.65/2.04  --bmc1_add_unsat_core                   none
% 11.65/2.04  --bmc1_unsat_core_children              false
% 11.65/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.04  --bmc1_out_stat                         full
% 11.65/2.04  --bmc1_ground_init                      false
% 11.65/2.04  --bmc1_pre_inst_next_state              false
% 11.65/2.04  --bmc1_pre_inst_state                   false
% 11.65/2.04  --bmc1_pre_inst_reach_state             false
% 11.65/2.04  --bmc1_out_unsat_core                   false
% 11.65/2.04  --bmc1_aig_witness_out                  false
% 11.65/2.04  --bmc1_verbose                          false
% 11.65/2.04  --bmc1_dump_clauses_tptp                false
% 11.65/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.04  --bmc1_dump_file                        -
% 11.65/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.04  --bmc1_ucm_extend_mode                  1
% 11.65/2.04  --bmc1_ucm_init_mode                    2
% 11.65/2.04  --bmc1_ucm_cone_mode                    none
% 11.65/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.04  --bmc1_ucm_relax_model                  4
% 11.65/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.04  --bmc1_ucm_layered_model                none
% 11.65/2.04  --bmc1_ucm_max_lemma_size               10
% 11.65/2.04  
% 11.65/2.04  ------ AIG Options
% 11.65/2.04  
% 11.65/2.04  --aig_mode                              false
% 11.65/2.04  
% 11.65/2.04  ------ Instantiation Options
% 11.65/2.04  
% 11.65/2.04  --instantiation_flag                    true
% 11.65/2.04  --inst_sos_flag                         false
% 11.65/2.04  --inst_sos_phase                        true
% 11.65/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.04  --inst_lit_sel_side                     num_symb
% 11.65/2.04  --inst_solver_per_active                1400
% 11.65/2.04  --inst_solver_calls_frac                1.
% 11.65/2.04  --inst_passive_queue_type               priority_queues
% 11.65/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.04  --inst_passive_queues_freq              [25;2]
% 11.65/2.04  --inst_dismatching                      true
% 11.65/2.04  --inst_eager_unprocessed_to_passive     true
% 11.65/2.04  --inst_prop_sim_given                   true
% 11.65/2.04  --inst_prop_sim_new                     false
% 11.65/2.04  --inst_subs_new                         false
% 11.65/2.04  --inst_eq_res_simp                      false
% 11.65/2.04  --inst_subs_given                       false
% 11.65/2.04  --inst_orphan_elimination               true
% 11.65/2.04  --inst_learning_loop_flag               true
% 11.65/2.04  --inst_learning_start                   3000
% 11.65/2.04  --inst_learning_factor                  2
% 11.65/2.04  --inst_start_prop_sim_after_learn       3
% 11.65/2.04  --inst_sel_renew                        solver
% 11.65/2.04  --inst_lit_activity_flag                true
% 11.65/2.04  --inst_restr_to_given                   false
% 11.65/2.04  --inst_activity_threshold               500
% 11.65/2.04  --inst_out_proof                        true
% 11.65/2.04  
% 11.65/2.04  ------ Resolution Options
% 11.65/2.04  
% 11.65/2.04  --resolution_flag                       true
% 11.65/2.04  --res_lit_sel                           adaptive
% 11.65/2.04  --res_lit_sel_side                      none
% 11.65/2.04  --res_ordering                          kbo
% 11.65/2.04  --res_to_prop_solver                    active
% 11.65/2.04  --res_prop_simpl_new                    false
% 11.65/2.04  --res_prop_simpl_given                  true
% 11.65/2.04  --res_passive_queue_type                priority_queues
% 11.65/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.04  --res_passive_queues_freq               [15;5]
% 11.65/2.04  --res_forward_subs                      full
% 11.65/2.04  --res_backward_subs                     full
% 11.65/2.04  --res_forward_subs_resolution           true
% 11.65/2.04  --res_backward_subs_resolution          true
% 11.65/2.04  --res_orphan_elimination                true
% 11.65/2.04  --res_time_limit                        2.
% 11.65/2.04  --res_out_proof                         true
% 11.65/2.04  
% 11.65/2.04  ------ Superposition Options
% 11.65/2.04  
% 11.65/2.04  --superposition_flag                    true
% 11.65/2.04  --sup_passive_queue_type                priority_queues
% 11.65/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.04  --demod_completeness_check              fast
% 11.65/2.04  --demod_use_ground                      true
% 11.65/2.04  --sup_to_prop_solver                    passive
% 11.65/2.04  --sup_prop_simpl_new                    true
% 11.65/2.04  --sup_prop_simpl_given                  true
% 11.65/2.04  --sup_fun_splitting                     false
% 11.65/2.04  --sup_smt_interval                      50000
% 11.65/2.04  
% 11.65/2.04  ------ Superposition Simplification Setup
% 11.65/2.04  
% 11.65/2.04  --sup_indices_passive                   []
% 11.65/2.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_full_bw                           [BwDemod]
% 11.65/2.04  --sup_immed_triv                        [TrivRules]
% 11.65/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_immed_bw_main                     []
% 11.65/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.04  
% 11.65/2.04  ------ Combination Options
% 11.65/2.04  
% 11.65/2.04  --comb_res_mult                         3
% 11.65/2.04  --comb_sup_mult                         2
% 11.65/2.04  --comb_inst_mult                        10
% 11.65/2.04  
% 11.65/2.04  ------ Debug Options
% 11.65/2.04  
% 11.65/2.04  --dbg_backtrace                         false
% 11.65/2.04  --dbg_dump_prop_clauses                 false
% 11.65/2.04  --dbg_dump_prop_clauses_file            -
% 11.65/2.04  --dbg_out_stat                          false
% 11.65/2.04  ------ Parsing...
% 11.65/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.04  ------ Proving...
% 11.65/2.04  ------ Problem Properties 
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  clauses                                 45
% 11.65/2.04  conjectures                             11
% 11.65/2.04  EPR                                     9
% 11.65/2.04  Horn                                    39
% 11.65/2.04  unary                                   16
% 11.65/2.04  binary                                  3
% 11.65/2.04  lits                                    135
% 11.65/2.04  lits eq                                 38
% 11.65/2.04  fd_pure                                 0
% 11.65/2.04  fd_pseudo                               0
% 11.65/2.04  fd_cond                                 5
% 11.65/2.04  fd_pseudo_cond                          2
% 11.65/2.04  AC symbols                              0
% 11.65/2.04  
% 11.65/2.04  ------ Schedule dynamic 5 is on 
% 11.65/2.04  
% 11.65/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  ------ 
% 11.65/2.04  Current options:
% 11.65/2.04  ------ 
% 11.65/2.04  
% 11.65/2.04  ------ Input Options
% 11.65/2.04  
% 11.65/2.04  --out_options                           all
% 11.65/2.04  --tptp_safe_out                         true
% 11.65/2.04  --problem_path                          ""
% 11.65/2.04  --include_path                          ""
% 11.65/2.04  --clausifier                            res/vclausify_rel
% 11.65/2.04  --clausifier_options                    --mode clausify
% 11.65/2.04  --stdin                                 false
% 11.65/2.04  --stats_out                             all
% 11.65/2.04  
% 11.65/2.04  ------ General Options
% 11.65/2.04  
% 11.65/2.04  --fof                                   false
% 11.65/2.04  --time_out_real                         305.
% 11.65/2.04  --time_out_virtual                      -1.
% 11.65/2.04  --symbol_type_check                     false
% 11.65/2.04  --clausify_out                          false
% 11.65/2.04  --sig_cnt_out                           false
% 11.65/2.04  --trig_cnt_out                          false
% 11.65/2.04  --trig_cnt_out_tolerance                1.
% 11.65/2.04  --trig_cnt_out_sk_spl                   false
% 11.65/2.04  --abstr_cl_out                          false
% 11.65/2.04  
% 11.65/2.04  ------ Global Options
% 11.65/2.04  
% 11.65/2.04  --schedule                              default
% 11.65/2.04  --add_important_lit                     false
% 11.65/2.04  --prop_solver_per_cl                    1000
% 11.65/2.04  --min_unsat_core                        false
% 11.65/2.04  --soft_assumptions                      false
% 11.65/2.04  --soft_lemma_size                       3
% 11.65/2.04  --prop_impl_unit_size                   0
% 11.65/2.04  --prop_impl_unit                        []
% 11.65/2.04  --share_sel_clauses                     true
% 11.65/2.04  --reset_solvers                         false
% 11.65/2.04  --bc_imp_inh                            [conj_cone]
% 11.65/2.04  --conj_cone_tolerance                   3.
% 11.65/2.04  --extra_neg_conj                        none
% 11.65/2.04  --large_theory_mode                     true
% 11.65/2.04  --prolific_symb_bound                   200
% 11.65/2.04  --lt_threshold                          2000
% 11.65/2.04  --clause_weak_htbl                      true
% 11.65/2.04  --gc_record_bc_elim                     false
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing Options
% 11.65/2.04  
% 11.65/2.04  --preprocessing_flag                    true
% 11.65/2.04  --time_out_prep_mult                    0.1
% 11.65/2.04  --splitting_mode                        input
% 11.65/2.04  --splitting_grd                         true
% 11.65/2.04  --splitting_cvd                         false
% 11.65/2.04  --splitting_cvd_svl                     false
% 11.65/2.04  --splitting_nvd                         32
% 11.65/2.04  --sub_typing                            true
% 11.65/2.04  --prep_gs_sim                           true
% 11.65/2.04  --prep_unflatten                        true
% 11.65/2.04  --prep_res_sim                          true
% 11.65/2.04  --prep_upred                            true
% 11.65/2.04  --prep_sem_filter                       exhaustive
% 11.65/2.04  --prep_sem_filter_out                   false
% 11.65/2.04  --pred_elim                             true
% 11.65/2.04  --res_sim_input                         true
% 11.65/2.04  --eq_ax_congr_red                       true
% 11.65/2.04  --pure_diseq_elim                       true
% 11.65/2.04  --brand_transform                       false
% 11.65/2.04  --non_eq_to_eq                          false
% 11.65/2.04  --prep_def_merge                        true
% 11.65/2.04  --prep_def_merge_prop_impl              false
% 11.65/2.04  --prep_def_merge_mbd                    true
% 11.65/2.04  --prep_def_merge_tr_red                 false
% 11.65/2.04  --prep_def_merge_tr_cl                  false
% 11.65/2.04  --smt_preprocessing                     true
% 11.65/2.04  --smt_ac_axioms                         fast
% 11.65/2.04  --preprocessed_out                      false
% 11.65/2.04  --preprocessed_stats                    false
% 11.65/2.04  
% 11.65/2.04  ------ Abstraction refinement Options
% 11.65/2.04  
% 11.65/2.04  --abstr_ref                             []
% 11.65/2.04  --abstr_ref_prep                        false
% 11.65/2.04  --abstr_ref_until_sat                   false
% 11.65/2.04  --abstr_ref_sig_restrict                funpre
% 11.65/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.04  --abstr_ref_under                       []
% 11.65/2.04  
% 11.65/2.04  ------ SAT Options
% 11.65/2.04  
% 11.65/2.04  --sat_mode                              false
% 11.65/2.04  --sat_fm_restart_options                ""
% 11.65/2.04  --sat_gr_def                            false
% 11.65/2.04  --sat_epr_types                         true
% 11.65/2.04  --sat_non_cyclic_types                  false
% 11.65/2.04  --sat_finite_models                     false
% 11.65/2.04  --sat_fm_lemmas                         false
% 11.65/2.04  --sat_fm_prep                           false
% 11.65/2.04  --sat_fm_uc_incr                        true
% 11.65/2.04  --sat_out_model                         small
% 11.65/2.04  --sat_out_clauses                       false
% 11.65/2.04  
% 11.65/2.04  ------ QBF Options
% 11.65/2.04  
% 11.65/2.04  --qbf_mode                              false
% 11.65/2.04  --qbf_elim_univ                         false
% 11.65/2.04  --qbf_dom_inst                          none
% 11.65/2.04  --qbf_dom_pre_inst                      false
% 11.65/2.04  --qbf_sk_in                             false
% 11.65/2.04  --qbf_pred_elim                         true
% 11.65/2.04  --qbf_split                             512
% 11.65/2.04  
% 11.65/2.04  ------ BMC1 Options
% 11.65/2.04  
% 11.65/2.04  --bmc1_incremental                      false
% 11.65/2.04  --bmc1_axioms                           reachable_all
% 11.65/2.04  --bmc1_min_bound                        0
% 11.65/2.04  --bmc1_max_bound                        -1
% 11.65/2.04  --bmc1_max_bound_default                -1
% 11.65/2.04  --bmc1_symbol_reachability              true
% 11.65/2.04  --bmc1_property_lemmas                  false
% 11.65/2.04  --bmc1_k_induction                      false
% 11.65/2.04  --bmc1_non_equiv_states                 false
% 11.65/2.04  --bmc1_deadlock                         false
% 11.65/2.04  --bmc1_ucm                              false
% 11.65/2.04  --bmc1_add_unsat_core                   none
% 11.65/2.04  --bmc1_unsat_core_children              false
% 11.65/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.04  --bmc1_out_stat                         full
% 11.65/2.04  --bmc1_ground_init                      false
% 11.65/2.04  --bmc1_pre_inst_next_state              false
% 11.65/2.04  --bmc1_pre_inst_state                   false
% 11.65/2.04  --bmc1_pre_inst_reach_state             false
% 11.65/2.04  --bmc1_out_unsat_core                   false
% 11.65/2.04  --bmc1_aig_witness_out                  false
% 11.65/2.04  --bmc1_verbose                          false
% 11.65/2.04  --bmc1_dump_clauses_tptp                false
% 11.65/2.04  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.04  --bmc1_dump_file                        -
% 11.65/2.04  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.04  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.04  --bmc1_ucm_extend_mode                  1
% 11.65/2.04  --bmc1_ucm_init_mode                    2
% 11.65/2.04  --bmc1_ucm_cone_mode                    none
% 11.65/2.04  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.04  --bmc1_ucm_relax_model                  4
% 11.65/2.04  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.04  --bmc1_ucm_layered_model                none
% 11.65/2.04  --bmc1_ucm_max_lemma_size               10
% 11.65/2.04  
% 11.65/2.04  ------ AIG Options
% 11.65/2.04  
% 11.65/2.04  --aig_mode                              false
% 11.65/2.04  
% 11.65/2.04  ------ Instantiation Options
% 11.65/2.04  
% 11.65/2.04  --instantiation_flag                    true
% 11.65/2.04  --inst_sos_flag                         false
% 11.65/2.04  --inst_sos_phase                        true
% 11.65/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.04  --inst_lit_sel_side                     none
% 11.65/2.04  --inst_solver_per_active                1400
% 11.65/2.04  --inst_solver_calls_frac                1.
% 11.65/2.04  --inst_passive_queue_type               priority_queues
% 11.65/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.04  --inst_passive_queues_freq              [25;2]
% 11.65/2.04  --inst_dismatching                      true
% 11.65/2.04  --inst_eager_unprocessed_to_passive     true
% 11.65/2.04  --inst_prop_sim_given                   true
% 11.65/2.04  --inst_prop_sim_new                     false
% 11.65/2.04  --inst_subs_new                         false
% 11.65/2.04  --inst_eq_res_simp                      false
% 11.65/2.04  --inst_subs_given                       false
% 11.65/2.04  --inst_orphan_elimination               true
% 11.65/2.04  --inst_learning_loop_flag               true
% 11.65/2.04  --inst_learning_start                   3000
% 11.65/2.04  --inst_learning_factor                  2
% 11.65/2.04  --inst_start_prop_sim_after_learn       3
% 11.65/2.04  --inst_sel_renew                        solver
% 11.65/2.04  --inst_lit_activity_flag                true
% 11.65/2.04  --inst_restr_to_given                   false
% 11.65/2.04  --inst_activity_threshold               500
% 11.65/2.04  --inst_out_proof                        true
% 11.65/2.04  
% 11.65/2.04  ------ Resolution Options
% 11.65/2.04  
% 11.65/2.04  --resolution_flag                       false
% 11.65/2.04  --res_lit_sel                           adaptive
% 11.65/2.04  --res_lit_sel_side                      none
% 11.65/2.04  --res_ordering                          kbo
% 11.65/2.04  --res_to_prop_solver                    active
% 11.65/2.04  --res_prop_simpl_new                    false
% 11.65/2.04  --res_prop_simpl_given                  true
% 11.65/2.04  --res_passive_queue_type                priority_queues
% 11.65/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.04  --res_passive_queues_freq               [15;5]
% 11.65/2.04  --res_forward_subs                      full
% 11.65/2.04  --res_backward_subs                     full
% 11.65/2.04  --res_forward_subs_resolution           true
% 11.65/2.04  --res_backward_subs_resolution          true
% 11.65/2.04  --res_orphan_elimination                true
% 11.65/2.04  --res_time_limit                        2.
% 11.65/2.04  --res_out_proof                         true
% 11.65/2.04  
% 11.65/2.04  ------ Superposition Options
% 11.65/2.04  
% 11.65/2.04  --superposition_flag                    true
% 11.65/2.04  --sup_passive_queue_type                priority_queues
% 11.65/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.04  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.04  --demod_completeness_check              fast
% 11.65/2.04  --demod_use_ground                      true
% 11.65/2.04  --sup_to_prop_solver                    passive
% 11.65/2.04  --sup_prop_simpl_new                    true
% 11.65/2.04  --sup_prop_simpl_given                  true
% 11.65/2.04  --sup_fun_splitting                     false
% 11.65/2.04  --sup_smt_interval                      50000
% 11.65/2.04  
% 11.65/2.04  ------ Superposition Simplification Setup
% 11.65/2.04  
% 11.65/2.04  --sup_indices_passive                   []
% 11.65/2.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_full_bw                           [BwDemod]
% 11.65/2.04  --sup_immed_triv                        [TrivRules]
% 11.65/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_immed_bw_main                     []
% 11.65/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.65/2.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.65/2.04  
% 11.65/2.04  ------ Combination Options
% 11.65/2.04  
% 11.65/2.04  --comb_res_mult                         3
% 11.65/2.04  --comb_sup_mult                         2
% 11.65/2.04  --comb_inst_mult                        10
% 11.65/2.04  
% 11.65/2.04  ------ Debug Options
% 11.65/2.04  
% 11.65/2.04  --dbg_backtrace                         false
% 11.65/2.04  --dbg_dump_prop_clauses                 false
% 11.65/2.04  --dbg_dump_prop_clauses_file            -
% 11.65/2.04  --dbg_out_stat                          false
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  ------ Proving...
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  % SZS status Theorem for theBenchmark.p
% 11.65/2.04  
% 11.65/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.04  
% 11.65/2.04  fof(f24,conjecture,(
% 11.65/2.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f25,negated_conjecture,(
% 11.65/2.04    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.65/2.04    inference(negated_conjecture,[],[f24])).
% 11.65/2.04  
% 11.65/2.04  fof(f58,plain,(
% 11.65/2.04    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.65/2.04    inference(ennf_transformation,[],[f25])).
% 11.65/2.04  
% 11.65/2.04  fof(f59,plain,(
% 11.65/2.04    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.65/2.04    inference(flattening,[],[f58])).
% 11.65/2.04  
% 11.65/2.04  fof(f66,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.65/2.04    introduced(choice_axiom,[])).
% 11.65/2.04  
% 11.65/2.04  fof(f65,plain,(
% 11.65/2.04    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.65/2.04    introduced(choice_axiom,[])).
% 11.65/2.04  
% 11.65/2.04  fof(f67,plain,(
% 11.65/2.04    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.65/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f66,f65])).
% 11.65/2.04  
% 11.65/2.04  fof(f109,plain,(
% 11.65/2.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f112,plain,(
% 11.65/2.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f20,axiom,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f52,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.65/2.04    inference(ennf_transformation,[],[f20])).
% 11.65/2.04  
% 11.65/2.04  fof(f53,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.65/2.04    inference(flattening,[],[f52])).
% 11.65/2.04  
% 11.65/2.04  fof(f100,plain,(
% 11.65/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f53])).
% 11.65/2.04  
% 11.65/2.04  fof(f110,plain,(
% 11.65/2.04    v1_funct_1(sK3)),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f107,plain,(
% 11.65/2.04    v1_funct_1(sK2)),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f17,axiom,(
% 11.65/2.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f48,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.65/2.04    inference(ennf_transformation,[],[f17])).
% 11.65/2.04  
% 11.65/2.04  fof(f49,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(flattening,[],[f48])).
% 11.65/2.04  
% 11.65/2.04  fof(f63,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(nnf_transformation,[],[f49])).
% 11.65/2.04  
% 11.65/2.04  fof(f91,plain,(
% 11.65/2.04    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f63])).
% 11.65/2.04  
% 11.65/2.04  fof(f114,plain,(
% 11.65/2.04    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f19,axiom,(
% 11.65/2.04    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f26,plain,(
% 11.65/2.04    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.65/2.04    inference(pure_predicate_removal,[],[f19])).
% 11.65/2.04  
% 11.65/2.04  fof(f99,plain,(
% 11.65/2.04    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f26])).
% 11.65/2.04  
% 11.65/2.04  fof(f16,axiom,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f46,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.65/2.04    inference(ennf_transformation,[],[f16])).
% 11.65/2.04  
% 11.65/2.04  fof(f47,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(flattening,[],[f46])).
% 11.65/2.04  
% 11.65/2.04  fof(f90,plain,(
% 11.65/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f47])).
% 11.65/2.04  
% 11.65/2.04  fof(f13,axiom,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f42,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.65/2.04    inference(ennf_transformation,[],[f13])).
% 11.65/2.04  
% 11.65/2.04  fof(f43,plain,(
% 11.65/2.04    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(flattening,[],[f42])).
% 11.65/2.04  
% 11.65/2.04  fof(f87,plain,(
% 11.65/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f43])).
% 11.65/2.04  
% 11.65/2.04  fof(f113,plain,(
% 11.65/2.04    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f23,axiom,(
% 11.65/2.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f56,plain,(
% 11.65/2.04    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.65/2.04    inference(ennf_transformation,[],[f23])).
% 11.65/2.04  
% 11.65/2.04  fof(f57,plain,(
% 11.65/2.04    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.65/2.04    inference(flattening,[],[f56])).
% 11.65/2.04  
% 11.65/2.04  fof(f106,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f57])).
% 11.65/2.04  
% 11.65/2.04  fof(f108,plain,(
% 11.65/2.04    v1_funct_2(sK2,sK0,sK1)),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f115,plain,(
% 11.65/2.04    v2_funct_1(sK2)),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f117,plain,(
% 11.65/2.04    k1_xboole_0 != sK1),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f10,axiom,(
% 11.65/2.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f37,plain,(
% 11.65/2.04    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.04    inference(ennf_transformation,[],[f10])).
% 11.65/2.04  
% 11.65/2.04  fof(f38,plain,(
% 11.65/2.04    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.04    inference(flattening,[],[f37])).
% 11.65/2.04  
% 11.65/2.04  fof(f83,plain,(
% 11.65/2.04    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f38])).
% 11.65/2.04  
% 11.65/2.04  fof(f2,axiom,(
% 11.65/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f28,plain,(
% 11.65/2.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.65/2.04    inference(ennf_transformation,[],[f2])).
% 11.65/2.04  
% 11.65/2.04  fof(f71,plain,(
% 11.65/2.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f28])).
% 11.65/2.04  
% 11.65/2.04  fof(f4,axiom,(
% 11.65/2.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f74,plain,(
% 11.65/2.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f4])).
% 11.65/2.04  
% 11.65/2.04  fof(f105,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f57])).
% 11.65/2.04  
% 11.65/2.04  fof(f5,axiom,(
% 11.65/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f30,plain,(
% 11.65/2.04    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.65/2.04    inference(ennf_transformation,[],[f5])).
% 11.65/2.04  
% 11.65/2.04  fof(f75,plain,(
% 11.65/2.04    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f30])).
% 11.65/2.04  
% 11.65/2.04  fof(f6,axiom,(
% 11.65/2.04    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f77,plain,(
% 11.65/2.04    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.65/2.04    inference(cnf_transformation,[],[f6])).
% 11.65/2.04  
% 11.65/2.04  fof(f21,axiom,(
% 11.65/2.04    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f101,plain,(
% 11.65/2.04    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f21])).
% 11.65/2.04  
% 11.65/2.04  fof(f119,plain,(
% 11.65/2.04    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.65/2.04    inference(definition_unfolding,[],[f77,f101])).
% 11.65/2.04  
% 11.65/2.04  fof(f7,axiom,(
% 11.65/2.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f31,plain,(
% 11.65/2.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.04    inference(ennf_transformation,[],[f7])).
% 11.65/2.04  
% 11.65/2.04  fof(f32,plain,(
% 11.65/2.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.04    inference(flattening,[],[f31])).
% 11.65/2.04  
% 11.65/2.04  fof(f78,plain,(
% 11.65/2.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f32])).
% 11.65/2.04  
% 11.65/2.04  fof(f12,axiom,(
% 11.65/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f27,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.65/2.04    inference(pure_predicate_removal,[],[f12])).
% 11.65/2.04  
% 11.65/2.04  fof(f41,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(ennf_transformation,[],[f27])).
% 11.65/2.04  
% 11.65/2.04  fof(f86,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f41])).
% 11.65/2.04  
% 11.65/2.04  fof(f3,axiom,(
% 11.65/2.04    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f29,plain,(
% 11.65/2.04    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.65/2.04    inference(ennf_transformation,[],[f3])).
% 11.65/2.04  
% 11.65/2.04  fof(f62,plain,(
% 11.65/2.04    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.65/2.04    inference(nnf_transformation,[],[f29])).
% 11.65/2.04  
% 11.65/2.04  fof(f72,plain,(
% 11.65/2.04    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f62])).
% 11.65/2.04  
% 11.65/2.04  fof(f1,axiom,(
% 11.65/2.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f60,plain,(
% 11.65/2.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.04    inference(nnf_transformation,[],[f1])).
% 11.65/2.04  
% 11.65/2.04  fof(f61,plain,(
% 11.65/2.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.04    inference(flattening,[],[f60])).
% 11.65/2.04  
% 11.65/2.04  fof(f70,plain,(
% 11.65/2.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f61])).
% 11.65/2.04  
% 11.65/2.04  fof(f8,axiom,(
% 11.65/2.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f33,plain,(
% 11.65/2.04    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.65/2.04    inference(ennf_transformation,[],[f8])).
% 11.65/2.04  
% 11.65/2.04  fof(f34,plain,(
% 11.65/2.04    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.65/2.04    inference(flattening,[],[f33])).
% 11.65/2.04  
% 11.65/2.04  fof(f80,plain,(
% 11.65/2.04    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f34])).
% 11.65/2.04  
% 11.65/2.04  fof(f121,plain,(
% 11.65/2.04    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.65/2.04    inference(definition_unfolding,[],[f80,f101,f101])).
% 11.65/2.04  
% 11.65/2.04  fof(f125,plain,(
% 11.65/2.04    ( ! [X2,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.65/2.04    inference(equality_resolution,[],[f121])).
% 11.65/2.04  
% 11.65/2.04  fof(f22,axiom,(
% 11.65/2.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f54,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.65/2.04    inference(ennf_transformation,[],[f22])).
% 11.65/2.04  
% 11.65/2.04  fof(f55,plain,(
% 11.65/2.04    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.65/2.04    inference(flattening,[],[f54])).
% 11.65/2.04  
% 11.65/2.04  fof(f102,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.65/2.04    inference(cnf_transformation,[],[f55])).
% 11.65/2.04  
% 11.65/2.04  fof(f18,axiom,(
% 11.65/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f50,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(ennf_transformation,[],[f18])).
% 11.65/2.04  
% 11.65/2.04  fof(f51,plain,(
% 11.65/2.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(flattening,[],[f50])).
% 11.65/2.04  
% 11.65/2.04  fof(f64,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(nnf_transformation,[],[f51])).
% 11.65/2.04  
% 11.65/2.04  fof(f93,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f64])).
% 11.65/2.04  
% 11.65/2.04  fof(f14,axiom,(
% 11.65/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.65/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.04  
% 11.65/2.04  fof(f44,plain,(
% 11.65/2.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.04    inference(ennf_transformation,[],[f14])).
% 11.65/2.04  
% 11.65/2.04  fof(f88,plain,(
% 11.65/2.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.04    inference(cnf_transformation,[],[f44])).
% 11.65/2.04  
% 11.65/2.04  fof(f111,plain,(
% 11.65/2.04    v1_funct_2(sK3,sK1,sK0)),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f116,plain,(
% 11.65/2.04    k1_xboole_0 != sK0),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  fof(f68,plain,(
% 11.65/2.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.65/2.04    inference(cnf_transformation,[],[f61])).
% 11.65/2.04  
% 11.65/2.04  fof(f124,plain,(
% 11.65/2.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.04    inference(equality_resolution,[],[f68])).
% 11.65/2.04  
% 11.65/2.04  fof(f118,plain,(
% 11.65/2.04    k2_funct_1(sK2) != sK3),
% 11.65/2.04    inference(cnf_transformation,[],[f67])).
% 11.65/2.04  
% 11.65/2.04  cnf(c_47,negated_conjecture,
% 11.65/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.65/2.04      inference(cnf_transformation,[],[f109]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2431,plain,
% 11.65/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_44,negated_conjecture,
% 11.65/2.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.65/2.04      inference(cnf_transformation,[],[f112]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2434,plain,
% 11.65/2.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_32,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X3)
% 11.65/2.04      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f100]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2441,plain,
% 11.65/2.04      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.65/2.04      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.65/2.04      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | v1_funct_1(X5) != iProver_top
% 11.65/2.04      | v1_funct_1(X4) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10250,plain,
% 11.65/2.04      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | v1_funct_1(X2) != iProver_top
% 11.65/2.04      | v1_funct_1(sK3) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2434,c_2441]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_46,negated_conjecture,
% 11.65/2.04      ( v1_funct_1(sK3) ),
% 11.65/2.04      inference(cnf_transformation,[],[f110]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_53,plain,
% 11.65/2.04      ( v1_funct_1(sK3) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10614,plain,
% 11.65/2.04      ( v1_funct_1(X2) != iProver_top
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_10250,c_53]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10615,plain,
% 11.65/2.04      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.04      inference(renaming,[status(thm)],[c_10614]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10626,plain,
% 11.65/2.04      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2431,c_10615]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_49,negated_conjecture,
% 11.65/2.04      ( v1_funct_1(sK2) ),
% 11.65/2.04      inference(cnf_transformation,[],[f107]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3051,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(sK3)
% 11.65/2.04      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_32]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3560,plain,
% 11.65/2.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.65/2.04      | ~ v1_funct_1(sK3)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3051]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4212,plain,
% 11.65/2.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.04      | ~ v1_funct_1(sK3)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3560]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_5833,plain,
% 11.65/2.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.04      | ~ v1_funct_1(sK3)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_4212]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10786,plain,
% 11.65/2.04      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_10626,c_49,c_47,c_46,c_44,c_5833]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_24,plain,
% 11.65/2.04      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.65/2.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.04      | X2 = X3 ),
% 11.65/2.04      inference(cnf_transformation,[],[f91]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_42,negated_conjecture,
% 11.65/2.04      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.65/2.04      inference(cnf_transformation,[],[f114]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_513,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | X0 = X3
% 11.65/2.04      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
% 11.65/2.04      | k6_partfun1(sK0) != X0
% 11.65/2.04      | sK0 != X2
% 11.65/2.04      | sK0 != X1 ),
% 11.65/2.04      inference(resolution_lifted,[status(thm)],[c_24,c_42]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_514,plain,
% 11.65/2.04      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.04      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.04      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.65/2.04      inference(unflattening,[status(thm)],[c_513]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_31,plain,
% 11.65/2.04      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.65/2.04      inference(cnf_transformation,[],[f99]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_522,plain,
% 11.65/2.04      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.04      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.65/2.04      inference(forward_subsumption_resolution,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_514,c_31]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2427,plain,
% 11.65/2.04      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.65/2.04      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10789,plain,
% 11.65/2.04      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.65/2.04      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.65/2.04      inference(demodulation,[status(thm)],[c_10786,c_2427]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_52,plain,
% 11.65/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_55,plain,
% 11.65/2.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_22,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.04      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f90]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2449,plain,
% 11.65/2.04      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.65/2.04      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.65/2.04      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_9253,plain,
% 11.65/2.04      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2434,c_2449]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_9757,plain,
% 11.65/2.04      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2431,c_9253]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_19,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.04      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 11.65/2.04      inference(cnf_transformation,[],[f87]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2452,plain,
% 11.65/2.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.04      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 11.65/2.04      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_9856,plain,
% 11.65/2.04      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 11.65/2.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.65/2.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_9757,c_2452]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_11727,plain,
% 11.65/2.04      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_10789,c_52,c_55,c_9856]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_43,negated_conjecture,
% 11.65/2.04      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.65/2.04      inference(cnf_transformation,[],[f113]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_36,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | k2_relset_1(X1,X2,X0) != X2
% 11.65/2.04      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 11.65/2.04      | k1_xboole_0 = X2 ),
% 11.65/2.04      inference(cnf_transformation,[],[f106]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2437,plain,
% 11.65/2.04      ( k2_relset_1(X0,X1,X2) != X1
% 11.65/2.04      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 11.65/2.04      | k1_xboole_0 = X1
% 11.65/2.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | v2_funct_1(X2) != iProver_top
% 11.65/2.04      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_5689,plain,
% 11.65/2.04      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.65/2.04      | sK1 = k1_xboole_0
% 11.65/2.04      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.65/2.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.65/2.04      | v2_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_43,c_2437]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_48,negated_conjecture,
% 11.65/2.04      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.65/2.04      inference(cnf_transformation,[],[f108]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_41,negated_conjecture,
% 11.65/2.04      ( v2_funct_1(sK2) ),
% 11.65/2.04      inference(cnf_transformation,[],[f115]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_39,negated_conjecture,
% 11.65/2.04      ( k1_xboole_0 != sK1 ),
% 11.65/2.04      inference(cnf_transformation,[],[f117]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3064,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,sK1)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.65/2.04      | ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | k2_relset_1(X1,sK1,X0) != sK1
% 11.65/2.04      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_36]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3535,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,X0,sK1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(X0,sK1,sK2) != sK1
% 11.65/2.04      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3064]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4024,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.65/2.04      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3535]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6202,plain,
% 11.65/2.04      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_5689,c_49,c_48,c_47,c_43,c_41,c_39,c_4024]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2435,plain,
% 11.65/2.04      ( v2_funct_1(sK2) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_14,plain,
% 11.65/2.04      ( ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_relat_1(X0)
% 11.65/2.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f83]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2456,plain,
% 11.65/2.04      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.65/2.04      | v2_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_5968,plain,
% 11.65/2.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2435,c_2456]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_928,plain,
% 11.65/2.04      ( ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_relat_1(X0)
% 11.65/2.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.65/2.04      | sK2 != X0 ),
% 11.65/2.04      inference(resolution_lifted,[status(thm)],[c_14,c_41]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_929,plain,
% 11.65/2.04      ( ~ v1_funct_1(sK2)
% 11.65/2.04      | ~ v1_relat_1(sK2)
% 11.65/2.04      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.65/2.04      inference(unflattening,[status(thm)],[c_928]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.04      | ~ v1_relat_1(X1)
% 11.65/2.04      | v1_relat_1(X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f71]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2842,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | v1_relat_1(X0)
% 11.65/2.04      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3454,plain,
% 11.65/2.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.04      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 11.65/2.04      | v1_relat_1(sK2) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_2842]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6,plain,
% 11.65/2.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.65/2.04      inference(cnf_transformation,[],[f74]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3966,plain,
% 11.65/2.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_6]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6369,plain,
% 11.65/2.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_5968,c_49,c_47,c_929,c_3454,c_3966]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_37,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | k2_relset_1(X1,X2,X0) != X2
% 11.65/2.04      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.65/2.04      | k1_xboole_0 = X2 ),
% 11.65/2.04      inference(cnf_transformation,[],[f105]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2436,plain,
% 11.65/2.04      ( k2_relset_1(X0,X1,X2) != X1
% 11.65/2.04      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.65/2.04      | k1_xboole_0 = X1
% 11.65/2.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.04      | v2_funct_1(X2) != iProver_top
% 11.65/2.04      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4481,plain,
% 11.65/2.04      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.65/2.04      | sK1 = k1_xboole_0
% 11.65/2.04      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.65/2.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.65/2.04      | v2_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_43,c_2436]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3074,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,sK1)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.65/2.04      | ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | k2_relset_1(X1,sK1,X0) != sK1
% 11.65/2.04      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_37]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3545,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,X0,sK1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(X0,sK1,sK2) != sK1
% 11.65/2.04      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3074]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4027,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.65/2.04      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.65/2.04      | k1_xboole_0 = sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3545]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4749,plain,
% 11.65/2.04      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_4481,c_49,c_48,c_47,c_43,c_41,c_39,c_4027]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_7,plain,
% 11.65/2.04      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 11.65/2.04      | ~ v1_relat_1(X0)
% 11.65/2.04      | ~ v1_relat_1(X1) ),
% 11.65/2.04      inference(cnf_transformation,[],[f75]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2461,plain,
% 11.65/2.04      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4752,plain,
% 11.65/2.04      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 11.65/2.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_4749,c_2461]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_8,plain,
% 11.65/2.04      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.65/2.04      inference(cnf_transformation,[],[f119]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4753,plain,
% 11.65/2.04      ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 11.65/2.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(demodulation,[status(thm)],[c_4752,c_8]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50,plain,
% 11.65/2.04      ( v1_funct_1(sK2) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_11,plain,
% 11.65/2.04      ( ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_relat_1(X0)
% 11.65/2.04      | v1_relat_1(k2_funct_1(X0)) ),
% 11.65/2.04      inference(cnf_transformation,[],[f78]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2831,plain,
% 11.65/2.04      ( ~ v1_funct_1(sK2)
% 11.65/2.04      | v1_relat_1(k2_funct_1(sK2))
% 11.65/2.04      | ~ v1_relat_1(sK2) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_11]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2832,plain,
% 11.65/2.04      ( v1_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3455,plain,
% 11.65/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.65/2.04      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_3454]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3967,plain,
% 11.65/2.04      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_3966]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4990,plain,
% 11.65/2.04      ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_4753,c_50,c_52,c_2832,c_3455,c_3967]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6373,plain,
% 11.65/2.04      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 11.65/2.04      inference(demodulation,[status(thm)],[c_6369,c_4990]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_18,plain,
% 11.65/2.04      ( v4_relat_1(X0,X1)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.65/2.04      inference(cnf_transformation,[],[f86]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_5,plain,
% 11.65/2.04      ( ~ v4_relat_1(X0,X1)
% 11.65/2.04      | r1_tarski(k1_relat_1(X0),X1)
% 11.65/2.04      | ~ v1_relat_1(X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f72]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_492,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | r1_tarski(k1_relat_1(X0),X1)
% 11.65/2.04      | ~ v1_relat_1(X0) ),
% 11.65/2.04      inference(resolution,[status(thm)],[c_18,c_5]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2428,plain,
% 11.65/2.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.04      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3518,plain,
% 11.65/2.04      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2431,c_2428]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_0,plain,
% 11.65/2.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.65/2.04      inference(cnf_transformation,[],[f70]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2465,plain,
% 11.65/2.04      ( X0 = X1
% 11.65/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.65/2.04      | r1_tarski(X1,X0) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4180,plain,
% 11.65/2.04      ( k1_relat_1(sK2) = sK0
% 11.65/2.04      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_3518,c_2465]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4296,plain,
% 11.65/2.04      ( r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top
% 11.65/2.04      | k1_relat_1(sK2) = sK0 ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_4180,c_52,c_3455,c_3967]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_4297,plain,
% 11.65/2.04      ( k1_relat_1(sK2) = sK0
% 11.65/2.04      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 11.65/2.04      inference(renaming,[status(thm)],[c_4296]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6389,plain,
% 11.65/2.04      ( k1_relat_1(sK2) = sK0 ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_6373,c_4297]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_7629,plain,
% 11.65/2.04      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 11.65/2.04      inference(demodulation,[status(thm)],[c_6389,c_6369]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_12,plain,
% 11.65/2.04      ( ~ v1_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X1)
% 11.65/2.04      | ~ v1_funct_1(X2)
% 11.65/2.04      | ~ v1_relat_1(X2)
% 11.65/2.04      | ~ v1_relat_1(X0)
% 11.65/2.04      | ~ v1_relat_1(X1)
% 11.65/2.04      | X0 = X2
% 11.65/2.04      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2))
% 11.65/2.04      | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 11.65/2.04      inference(cnf_transformation,[],[f125]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2458,plain,
% 11.65/2.04      ( X0 = X1
% 11.65/2.04      | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
% 11.65/2.04      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(X1) != iProver_top
% 11.65/2.04      | v1_funct_1(X2) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X2) != iProver_top
% 11.65/2.04      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_10325,plain,
% 11.65/2.04      ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 11.65/2.04      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 11.65/2.04      | k2_funct_1(sK2) = X1
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(X1) != iProver_top
% 11.65/2.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X1) != iProver_top
% 11.65/2.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_7629,c_2458]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_51,plain,
% 11.65/2.04      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_57,plain,
% 11.65/2.04      ( v2_funct_1(sK2) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_35,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | ~ v2_funct_1(X0)
% 11.65/2.04      | ~ v1_funct_1(X0)
% 11.65/2.04      | v1_funct_1(k2_funct_1(X0))
% 11.65/2.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.65/2.04      inference(cnf_transformation,[],[f102]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3012,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,X0,X1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | v1_funct_1(k2_funct_1(sK2))
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(X0,X1,sK2) != X1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_35]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3419,plain,
% 11.65/2.04      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.65/2.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.65/2.04      | ~ v2_funct_1(sK2)
% 11.65/2.04      | v1_funct_1(k2_funct_1(sK2))
% 11.65/2.04      | ~ v1_funct_1(sK2)
% 11.65/2.04      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_3012]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3420,plain,
% 11.65/2.04      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 11.65/2.04      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.65/2.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.65/2.04      | v2_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_3419]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_49821,plain,
% 11.65/2.04      ( v1_relat_1(X1) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 11.65/2.04      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 11.65/2.04      | k2_funct_1(sK2) = X1
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(X1) != iProver_top ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_10325,c_50,c_51,c_52,c_43,c_57,c_2832,c_3420,c_3455,
% 11.65/2.04                 c_3967]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_49822,plain,
% 11.65/2.04      ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 11.65/2.04      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 11.65/2.04      | k2_funct_1(sK2) = X1
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(X1) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.04      inference(renaming,[status(thm)],[c_49821]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_49834,plain,
% 11.65/2.04      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 11.65/2.04      | k2_funct_1(sK2) = X0
% 11.65/2.04      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_funct_1(sK2) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_6202,c_49822]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50006,plain,
% 11.65/2.04      ( v1_relat_1(X0) != iProver_top
% 11.65/2.04      | k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 11.65/2.04      | k2_funct_1(sK2) = X0
% 11.65/2.04      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 11.65/2.04      | v1_funct_1(X0) != iProver_top ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_49834,c_50,c_52,c_3455,c_3967]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50007,plain,
% 11.65/2.04      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 11.65/2.04      | k2_funct_1(sK2) = X0
% 11.65/2.04      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 11.65/2.04      | v1_funct_1(X0) != iProver_top
% 11.65/2.04      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.04      inference(renaming,[status(thm)],[c_50006]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50018,plain,
% 11.65/2.04      ( k2_funct_1(sK2) = sK3
% 11.65/2.04      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 11.65/2.04      | v1_funct_1(sK3) != iProver_top
% 11.65/2.04      | v1_relat_1(sK3) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_11727,c_50007]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_30,plain,
% 11.65/2.04      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | k1_relset_1(X1,X2,X0) = X1
% 11.65/2.04      | k1_xboole_0 = X2 ),
% 11.65/2.04      inference(cnf_transformation,[],[f93]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2443,plain,
% 11.65/2.04      ( k1_relset_1(X0,X1,X2) = X0
% 11.65/2.04      | k1_xboole_0 = X1
% 11.65/2.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6969,plain,
% 11.65/2.04      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 11.65/2.04      | sK0 = k1_xboole_0
% 11.65/2.04      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2434,c_2443]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_20,plain,
% 11.65/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f88]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2451,plain,
% 11.65/2.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.65/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3579,plain,
% 11.65/2.04      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 11.65/2.04      inference(superposition,[status(thm)],[c_2434,c_2451]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_6978,plain,
% 11.65/2.04      ( k1_relat_1(sK3) = sK1
% 11.65/2.04      | sK0 = k1_xboole_0
% 11.65/2.04      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 11.65/2.04      inference(demodulation,[status(thm)],[c_6969,c_3579]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_45,negated_conjecture,
% 11.65/2.04      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f111]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_54,plain,
% 11.65/2.04      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_40,negated_conjecture,
% 11.65/2.04      ( k1_xboole_0 != sK0 ),
% 11.65/2.04      inference(cnf_transformation,[],[f116]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2,plain,
% 11.65/2.04      ( r1_tarski(X0,X0) ),
% 11.65/2.04      inference(cnf_transformation,[],[f124]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_158,plain,
% 11.65/2.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_2]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_162,plain,
% 11.65/2.04      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.65/2.04      | k1_xboole_0 = k1_xboole_0 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_0]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_1762,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2913,plain,
% 11.65/2.04      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_1762]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_2914,plain,
% 11.65/2.04      ( sK0 != k1_xboole_0
% 11.65/2.04      | k1_xboole_0 = sK0
% 11.65/2.04      | k1_xboole_0 != k1_xboole_0 ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_2913]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_7386,plain,
% 11.65/2.04      ( k1_relat_1(sK3) = sK1 ),
% 11.65/2.04      inference(global_propositional_subsumption,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_6978,c_54,c_40,c_158,c_162,c_2914]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50023,plain,
% 11.65/2.04      ( k2_funct_1(sK2) = sK3
% 11.65/2.04      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 11.65/2.04      | v1_funct_1(sK3) != iProver_top
% 11.65/2.04      | v1_relat_1(sK3) != iProver_top ),
% 11.65/2.04      inference(light_normalisation,[status(thm)],[c_50018,c_7386]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_50024,plain,
% 11.65/2.04      ( k2_funct_1(sK2) = sK3
% 11.65/2.04      | v1_funct_1(sK3) != iProver_top
% 11.65/2.04      | v1_relat_1(sK3) != iProver_top ),
% 11.65/2.04      inference(equality_resolution_simp,[status(thm)],[c_50023]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3954,plain,
% 11.65/2.04      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_6]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3955,plain,
% 11.65/2.04      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_3954]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3451,plain,
% 11.65/2.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.65/2.04      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 11.65/2.04      | v1_relat_1(sK3) ),
% 11.65/2.04      inference(instantiation,[status(thm)],[c_2842]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_3452,plain,
% 11.65/2.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.65/2.04      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.65/2.04      | v1_relat_1(sK3) = iProver_top ),
% 11.65/2.04      inference(predicate_to_equality,[status(thm)],[c_3451]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(c_38,negated_conjecture,
% 11.65/2.04      ( k2_funct_1(sK2) != sK3 ),
% 11.65/2.04      inference(cnf_transformation,[],[f118]) ).
% 11.65/2.04  
% 11.65/2.04  cnf(contradiction,plain,
% 11.65/2.04      ( $false ),
% 11.65/2.04      inference(minisat,
% 11.65/2.04                [status(thm)],
% 11.65/2.04                [c_50024,c_3955,c_3452,c_38,c_55,c_53]) ).
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.04  
% 11.65/2.04  ------                               Statistics
% 11.65/2.04  
% 11.65/2.04  ------ General
% 11.65/2.04  
% 11.65/2.04  abstr_ref_over_cycles:                  0
% 11.65/2.04  abstr_ref_under_cycles:                 0
% 11.65/2.04  gc_basic_clause_elim:                   0
% 11.65/2.04  forced_gc_time:                         0
% 11.65/2.04  parsing_time:                           0.008
% 11.65/2.04  unif_index_cands_time:                  0.
% 11.65/2.04  unif_index_add_time:                    0.
% 11.65/2.04  orderings_time:                         0.
% 11.65/2.04  out_proof_time:                         0.02
% 11.65/2.04  total_time:                             1.475
% 11.65/2.04  num_of_symbols:                         55
% 11.65/2.04  num_of_terms:                           62231
% 11.65/2.04  
% 11.65/2.04  ------ Preprocessing
% 11.65/2.04  
% 11.65/2.04  num_of_splits:                          0
% 11.65/2.04  num_of_split_atoms:                     0
% 11.65/2.04  num_of_reused_defs:                     0
% 11.65/2.04  num_eq_ax_congr_red:                    26
% 11.65/2.04  num_of_sem_filtered_clauses:            1
% 11.65/2.04  num_of_subtypes:                        0
% 11.65/2.04  monotx_restored_types:                  0
% 11.65/2.04  sat_num_of_epr_types:                   0
% 11.65/2.04  sat_num_of_non_cyclic_types:            0
% 11.65/2.04  sat_guarded_non_collapsed_types:        0
% 11.65/2.04  num_pure_diseq_elim:                    0
% 11.65/2.04  simp_replaced_by:                       0
% 11.65/2.04  res_preprocessed:                       221
% 11.65/2.04  prep_upred:                             0
% 11.65/2.04  prep_unflattend:                        26
% 11.65/2.04  smt_new_axioms:                         0
% 11.65/2.04  pred_elim_cands:                        6
% 11.65/2.04  pred_elim:                              2
% 11.65/2.04  pred_elim_cl:                           4
% 11.65/2.04  pred_elim_cycles:                       4
% 11.65/2.04  merged_defs:                            0
% 11.65/2.04  merged_defs_ncl:                        0
% 11.65/2.04  bin_hyper_res:                          0
% 11.65/2.04  prep_cycles:                            4
% 11.65/2.04  pred_elim_time:                         0.014
% 11.65/2.04  splitting_time:                         0.
% 11.65/2.04  sem_filter_time:                        0.
% 11.65/2.04  monotx_time:                            0.
% 11.65/2.04  subtype_inf_time:                       0.
% 11.65/2.04  
% 11.65/2.04  ------ Problem properties
% 11.65/2.04  
% 11.65/2.04  clauses:                                45
% 11.65/2.04  conjectures:                            11
% 11.65/2.04  epr:                                    9
% 11.65/2.04  horn:                                   39
% 11.65/2.04  ground:                                 12
% 11.65/2.04  unary:                                  16
% 11.65/2.04  binary:                                 3
% 11.65/2.04  lits:                                   135
% 11.65/2.04  lits_eq:                                38
% 11.65/2.04  fd_pure:                                0
% 11.65/2.04  fd_pseudo:                              0
% 11.65/2.04  fd_cond:                                5
% 11.65/2.04  fd_pseudo_cond:                         2
% 11.65/2.04  ac_symbols:                             0
% 11.65/2.04  
% 11.65/2.04  ------ Propositional Solver
% 11.65/2.04  
% 11.65/2.04  prop_solver_calls:                      33
% 11.65/2.04  prop_fast_solver_calls:                 2769
% 11.65/2.04  smt_solver_calls:                       0
% 11.65/2.04  smt_fast_solver_calls:                  0
% 11.65/2.04  prop_num_of_clauses:                    17744
% 11.65/2.04  prop_preprocess_simplified:             33894
% 11.65/2.04  prop_fo_subsumed:                       236
% 11.65/2.04  prop_solver_time:                       0.
% 11.65/2.04  smt_solver_time:                        0.
% 11.65/2.04  smt_fast_solver_time:                   0.
% 11.65/2.04  prop_fast_solver_time:                  0.
% 11.65/2.04  prop_unsat_core_time:                   0.002
% 11.65/2.04  
% 11.65/2.04  ------ QBF
% 11.65/2.04  
% 11.65/2.04  qbf_q_res:                              0
% 11.65/2.04  qbf_num_tautologies:                    0
% 11.65/2.04  qbf_prep_cycles:                        0
% 11.65/2.04  
% 11.65/2.04  ------ BMC1
% 11.65/2.04  
% 11.65/2.04  bmc1_current_bound:                     -1
% 11.65/2.04  bmc1_last_solved_bound:                 -1
% 11.65/2.04  bmc1_unsat_core_size:                   -1
% 11.65/2.04  bmc1_unsat_core_parents_size:           -1
% 11.65/2.04  bmc1_merge_next_fun:                    0
% 11.65/2.04  bmc1_unsat_core_clauses_time:           0.
% 11.65/2.04  
% 11.65/2.04  ------ Instantiation
% 11.65/2.04  
% 11.65/2.04  inst_num_of_clauses:                    4611
% 11.65/2.04  inst_num_in_passive:                    2525
% 11.65/2.04  inst_num_in_active:                     1959
% 11.65/2.04  inst_num_in_unprocessed:                133
% 11.65/2.04  inst_num_of_loops:                      2120
% 11.65/2.04  inst_num_of_learning_restarts:          0
% 11.65/2.04  inst_num_moves_active_passive:          159
% 11.65/2.04  inst_lit_activity:                      0
% 11.65/2.04  inst_lit_activity_moves:                3
% 11.65/2.04  inst_num_tautologies:                   0
% 11.65/2.04  inst_num_prop_implied:                  0
% 11.65/2.04  inst_num_existing_simplified:           0
% 11.65/2.04  inst_num_eq_res_simplified:             0
% 11.65/2.04  inst_num_child_elim:                    0
% 11.65/2.04  inst_num_of_dismatching_blockings:      3555
% 11.65/2.04  inst_num_of_non_proper_insts:           5091
% 11.65/2.04  inst_num_of_duplicates:                 0
% 11.65/2.04  inst_inst_num_from_inst_to_res:         0
% 11.65/2.04  inst_dismatching_checking_time:         0.
% 11.65/2.04  
% 11.65/2.04  ------ Resolution
% 11.65/2.04  
% 11.65/2.04  res_num_of_clauses:                     0
% 11.65/2.04  res_num_in_passive:                     0
% 11.65/2.04  res_num_in_active:                      0
% 11.65/2.04  res_num_of_loops:                       225
% 11.65/2.04  res_forward_subset_subsumed:            190
% 11.65/2.04  res_backward_subset_subsumed:           20
% 11.65/2.04  res_forward_subsumed:                   2
% 11.65/2.04  res_backward_subsumed:                  0
% 11.65/2.04  res_forward_subsumption_resolution:     1
% 11.65/2.04  res_backward_subsumption_resolution:    0
% 11.65/2.04  res_clause_to_clause_subsumption:       3107
% 11.65/2.04  res_orphan_elimination:                 0
% 11.65/2.04  res_tautology_del:                      87
% 11.65/2.04  res_num_eq_res_simplified:              0
% 11.65/2.04  res_num_sel_changes:                    0
% 11.65/2.04  res_moves_from_active_to_pass:          0
% 11.65/2.04  
% 11.65/2.04  ------ Superposition
% 11.65/2.04  
% 11.65/2.04  sup_time_total:                         0.
% 11.65/2.04  sup_time_generating:                    0.
% 11.65/2.04  sup_time_sim_full:                      0.
% 11.65/2.04  sup_time_sim_immed:                     0.
% 11.65/2.04  
% 11.65/2.04  sup_num_of_clauses:                     1567
% 11.65/2.04  sup_num_in_active:                      410
% 11.65/2.04  sup_num_in_passive:                     1157
% 11.65/2.04  sup_num_of_loops:                       423
% 11.65/2.04  sup_fw_superposition:                   893
% 11.65/2.04  sup_bw_superposition:                   801
% 11.65/2.04  sup_immediate_simplified:               605
% 11.65/2.04  sup_given_eliminated:                   1
% 11.65/2.04  comparisons_done:                       0
% 11.65/2.04  comparisons_avoided:                    5
% 11.65/2.04  
% 11.65/2.04  ------ Simplifications
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  sim_fw_subset_subsumed:                 28
% 11.65/2.04  sim_bw_subset_subsumed:                 16
% 11.65/2.04  sim_fw_subsumed:                        39
% 11.65/2.04  sim_bw_subsumed:                        0
% 11.65/2.04  sim_fw_subsumption_res:                 6
% 11.65/2.04  sim_bw_subsumption_res:                 0
% 11.65/2.04  sim_tautology_del:                      0
% 11.65/2.04  sim_eq_tautology_del:                   62
% 11.65/2.04  sim_eq_res_simp:                        2
% 11.65/2.04  sim_fw_demodulated:                     126
% 11.65/2.04  sim_bw_demodulated:                     14
% 11.65/2.04  sim_light_normalised:                   460
% 11.65/2.04  sim_joinable_taut:                      0
% 11.65/2.04  sim_joinable_simp:                      0
% 11.65/2.04  sim_ac_normalised:                      0
% 11.65/2.04  sim_smt_subsumption:                    0
% 11.65/2.04  
%------------------------------------------------------------------------------
