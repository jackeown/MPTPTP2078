%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:26 EST 2020

% Result     : Theorem 12.09s
% Output     : CNFRefutation 12.09s
% Verified   : 
% Statistics : Number of formulae       :  204 (1250 expanded)
%              Number of clauses        :  123 ( 360 expanded)
%              Number of leaves         :   22 ( 320 expanded)
%              Depth                    :   22
%              Number of atoms          :  795 (10131 expanded)
%              Number of equality atoms :  376 (3666 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f56,plain,(
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

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f62,f61])).

fof(f111,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f104,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f50])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f108,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f113,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f119,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f75,f93])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2)
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f93,f93])).

fof(f22,axiom,(
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

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_854,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_39805,plain,
    ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | sK2 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_844,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3244,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_7587,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3244])).

cnf(c_19732,plain,
    ( k2_funct_1(sK3) != sK2
    | sK2 = k2_funct_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7587])).

cnf(c_1560,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_18639,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
    | k6_partfun1(sK0) != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_43])).

cnf(c_518,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_526,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_518,c_25])).

cnf(c_1470,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1938,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2592,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1470,c_50,c_48,c_47,c_45,c_526,c_1938])).

cnf(c_44,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1485,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9055,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_44,c_1485])).

cnf(c_51,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_52,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_9280,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9055,c_51,c_52,c_53])).

cnf(c_9281,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9280])).

cnf(c_9284,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2592,c_9281])).

cnf(c_54,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_55,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_41,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_154,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_158,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1598,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1599,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3229,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3230,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3229])).

cnf(c_9613,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9284,c_54,c_55,c_56,c_41,c_154,c_158,c_1599,c_3230])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1496,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9622,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9613,c_1496])).

cnf(c_1477,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1491,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3025,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1477,c_1491])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_530,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_43])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_624,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_531])).

cnf(c_1469,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_2084,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1469])).

cnf(c_2599,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2084,c_51,c_52,c_53,c_54,c_55,c_56])).

cnf(c_3028,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3025,c_2599])).

cnf(c_9625,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9622,c_3028])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1687,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1962,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2691,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_2692,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2691])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2989,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2990,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2989])).

cnf(c_17200,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9625,c_54,c_56,c_2692,c_2990])).

cnf(c_1474,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1487,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6037,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_1487])).

cnf(c_6203,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6037,c_54])).

cnf(c_6204,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6203])).

cnf(c_6213,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_6204])).

cnf(c_6216,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6213,c_2592])).

cnf(c_7632,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6216,c_51])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | X2 = X0
    | k5_relat_1(X3,X2) != k6_partfun1(X1)
    | k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X2)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1503,plain,
    ( X0 = X1
    | k5_relat_1(X2,X0) != k6_partfun1(X3)
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | r1_tarski(k2_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7634,plain,
    ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
    | sK2 = X0
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7632,c_1503])).

cnf(c_3026,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1474,c_1491])).

cnf(c_3027,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3026,c_44])).

cnf(c_7635,plain,
    ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
    | sK2 = X0
    | r1_tarski(sK1,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7634,c_3027])).

cnf(c_1504,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1505,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3167,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_1505])).

cnf(c_3331,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_3167])).

cnf(c_8334,plain,
    ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
    | sK2 = X0
    | r1_tarski(sK1,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7635,c_56,c_2692,c_2990,c_3331])).

cnf(c_17213,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_partfun1(X0)
    | k2_funct_1(sK3) = sK2
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17200,c_8334])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1481,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3548,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_1481])).

cnf(c_5799,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_54,c_55,c_56,c_41,c_154,c_158,c_1599])).

cnf(c_5800,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5799])).

cnf(c_9624,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_9613,c_5800])).

cnf(c_17219,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(X0) != k6_partfun1(sK1)
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17213,c_9624])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3065,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3066,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3065])).

cnf(c_17703,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | k6_partfun1(X0) != k6_partfun1(sK1)
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17219,c_54,c_56,c_2692,c_2990,c_3066])).

cnf(c_17704,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(X0) != k6_partfun1(sK1)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17703])).

cnf(c_17709,plain,
    ( k2_funct_1(sK3) = sK2
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_17704])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4336,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4337,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4336])).

cnf(c_4207,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1657,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_2073,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_3482,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2190,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3232,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2605,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2606,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2605])).

cnf(c_2601,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1651,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2054,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_39,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39805,c_19732,c_18639,c_17709,c_9284,c_4337,c_4207,c_3482,c_3232,c_3230,c_2990,c_2692,c_2606,c_2601,c_2054,c_1599,c_158,c_154,c_39,c_41,c_56,c_55,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.09/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.09/1.98  
% 12.09/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.09/1.98  
% 12.09/1.98  ------  iProver source info
% 12.09/1.98  
% 12.09/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.09/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.09/1.98  git: non_committed_changes: false
% 12.09/1.98  git: last_make_outside_of_git: false
% 12.09/1.98  
% 12.09/1.98  ------ 
% 12.09/1.98  
% 12.09/1.98  ------ Input Options
% 12.09/1.98  
% 12.09/1.98  --out_options                           all
% 12.09/1.98  --tptp_safe_out                         true
% 12.09/1.98  --problem_path                          ""
% 12.09/1.98  --include_path                          ""
% 12.09/1.98  --clausifier                            res/vclausify_rel
% 12.09/1.98  --clausifier_options                    ""
% 12.09/1.98  --stdin                                 false
% 12.09/1.98  --stats_out                             all
% 12.09/1.98  
% 12.09/1.98  ------ General Options
% 12.09/1.98  
% 12.09/1.98  --fof                                   false
% 12.09/1.98  --time_out_real                         305.
% 12.09/1.98  --time_out_virtual                      -1.
% 12.09/1.98  --symbol_type_check                     false
% 12.09/1.98  --clausify_out                          false
% 12.09/1.98  --sig_cnt_out                           false
% 12.09/1.98  --trig_cnt_out                          false
% 12.09/1.98  --trig_cnt_out_tolerance                1.
% 12.09/1.98  --trig_cnt_out_sk_spl                   false
% 12.09/1.98  --abstr_cl_out                          false
% 12.09/1.98  
% 12.09/1.98  ------ Global Options
% 12.09/1.98  
% 12.09/1.98  --schedule                              default
% 12.09/1.98  --add_important_lit                     false
% 12.09/1.98  --prop_solver_per_cl                    1000
% 12.09/1.98  --min_unsat_core                        false
% 12.09/1.98  --soft_assumptions                      false
% 12.09/1.98  --soft_lemma_size                       3
% 12.09/1.98  --prop_impl_unit_size                   0
% 12.09/1.98  --prop_impl_unit                        []
% 12.09/1.98  --share_sel_clauses                     true
% 12.09/1.98  --reset_solvers                         false
% 12.09/1.98  --bc_imp_inh                            [conj_cone]
% 12.09/1.98  --conj_cone_tolerance                   3.
% 12.09/1.98  --extra_neg_conj                        none
% 12.09/1.98  --large_theory_mode                     true
% 12.09/1.98  --prolific_symb_bound                   200
% 12.09/1.98  --lt_threshold                          2000
% 12.09/1.98  --clause_weak_htbl                      true
% 12.09/1.98  --gc_record_bc_elim                     false
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing Options
% 12.09/1.98  
% 12.09/1.98  --preprocessing_flag                    true
% 12.09/1.98  --time_out_prep_mult                    0.1
% 12.09/1.98  --splitting_mode                        input
% 12.09/1.98  --splitting_grd                         true
% 12.09/1.98  --splitting_cvd                         false
% 12.09/1.98  --splitting_cvd_svl                     false
% 12.09/1.98  --splitting_nvd                         32
% 12.09/1.98  --sub_typing                            true
% 12.09/1.98  --prep_gs_sim                           true
% 12.09/1.98  --prep_unflatten                        true
% 12.09/1.98  --prep_res_sim                          true
% 12.09/1.98  --prep_upred                            true
% 12.09/1.98  --prep_sem_filter                       exhaustive
% 12.09/1.98  --prep_sem_filter_out                   false
% 12.09/1.98  --pred_elim                             true
% 12.09/1.98  --res_sim_input                         true
% 12.09/1.98  --eq_ax_congr_red                       true
% 12.09/1.98  --pure_diseq_elim                       true
% 12.09/1.98  --brand_transform                       false
% 12.09/1.98  --non_eq_to_eq                          false
% 12.09/1.98  --prep_def_merge                        true
% 12.09/1.98  --prep_def_merge_prop_impl              false
% 12.09/1.98  --prep_def_merge_mbd                    true
% 12.09/1.98  --prep_def_merge_tr_red                 false
% 12.09/1.98  --prep_def_merge_tr_cl                  false
% 12.09/1.98  --smt_preprocessing                     true
% 12.09/1.98  --smt_ac_axioms                         fast
% 12.09/1.98  --preprocessed_out                      false
% 12.09/1.98  --preprocessed_stats                    false
% 12.09/1.98  
% 12.09/1.98  ------ Abstraction refinement Options
% 12.09/1.98  
% 12.09/1.98  --abstr_ref                             []
% 12.09/1.98  --abstr_ref_prep                        false
% 12.09/1.98  --abstr_ref_until_sat                   false
% 12.09/1.98  --abstr_ref_sig_restrict                funpre
% 12.09/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.09/1.98  --abstr_ref_under                       []
% 12.09/1.98  
% 12.09/1.98  ------ SAT Options
% 12.09/1.98  
% 12.09/1.98  --sat_mode                              false
% 12.09/1.98  --sat_fm_restart_options                ""
% 12.09/1.98  --sat_gr_def                            false
% 12.09/1.98  --sat_epr_types                         true
% 12.09/1.98  --sat_non_cyclic_types                  false
% 12.09/1.98  --sat_finite_models                     false
% 12.09/1.98  --sat_fm_lemmas                         false
% 12.09/1.98  --sat_fm_prep                           false
% 12.09/1.98  --sat_fm_uc_incr                        true
% 12.09/1.98  --sat_out_model                         small
% 12.09/1.98  --sat_out_clauses                       false
% 12.09/1.98  
% 12.09/1.98  ------ QBF Options
% 12.09/1.98  
% 12.09/1.98  --qbf_mode                              false
% 12.09/1.98  --qbf_elim_univ                         false
% 12.09/1.98  --qbf_dom_inst                          none
% 12.09/1.98  --qbf_dom_pre_inst                      false
% 12.09/1.98  --qbf_sk_in                             false
% 12.09/1.98  --qbf_pred_elim                         true
% 12.09/1.98  --qbf_split                             512
% 12.09/1.98  
% 12.09/1.98  ------ BMC1 Options
% 12.09/1.98  
% 12.09/1.98  --bmc1_incremental                      false
% 12.09/1.98  --bmc1_axioms                           reachable_all
% 12.09/1.98  --bmc1_min_bound                        0
% 12.09/1.98  --bmc1_max_bound                        -1
% 12.09/1.98  --bmc1_max_bound_default                -1
% 12.09/1.98  --bmc1_symbol_reachability              true
% 12.09/1.98  --bmc1_property_lemmas                  false
% 12.09/1.98  --bmc1_k_induction                      false
% 12.09/1.98  --bmc1_non_equiv_states                 false
% 12.09/1.98  --bmc1_deadlock                         false
% 12.09/1.98  --bmc1_ucm                              false
% 12.09/1.98  --bmc1_add_unsat_core                   none
% 12.09/1.98  --bmc1_unsat_core_children              false
% 12.09/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.09/1.98  --bmc1_out_stat                         full
% 12.09/1.98  --bmc1_ground_init                      false
% 12.09/1.98  --bmc1_pre_inst_next_state              false
% 12.09/1.98  --bmc1_pre_inst_state                   false
% 12.09/1.98  --bmc1_pre_inst_reach_state             false
% 12.09/1.98  --bmc1_out_unsat_core                   false
% 12.09/1.98  --bmc1_aig_witness_out                  false
% 12.09/1.98  --bmc1_verbose                          false
% 12.09/1.98  --bmc1_dump_clauses_tptp                false
% 12.09/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.09/1.98  --bmc1_dump_file                        -
% 12.09/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.09/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.09/1.98  --bmc1_ucm_extend_mode                  1
% 12.09/1.98  --bmc1_ucm_init_mode                    2
% 12.09/1.98  --bmc1_ucm_cone_mode                    none
% 12.09/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.09/1.98  --bmc1_ucm_relax_model                  4
% 12.09/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.09/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.09/1.98  --bmc1_ucm_layered_model                none
% 12.09/1.98  --bmc1_ucm_max_lemma_size               10
% 12.09/1.98  
% 12.09/1.98  ------ AIG Options
% 12.09/1.98  
% 12.09/1.98  --aig_mode                              false
% 12.09/1.98  
% 12.09/1.98  ------ Instantiation Options
% 12.09/1.98  
% 12.09/1.98  --instantiation_flag                    true
% 12.09/1.98  --inst_sos_flag                         true
% 12.09/1.98  --inst_sos_phase                        true
% 12.09/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.09/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.09/1.98  --inst_lit_sel_side                     num_symb
% 12.09/1.98  --inst_solver_per_active                1400
% 12.09/1.98  --inst_solver_calls_frac                1.
% 12.09/1.98  --inst_passive_queue_type               priority_queues
% 12.09/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.09/1.98  --inst_passive_queues_freq              [25;2]
% 12.09/1.98  --inst_dismatching                      true
% 12.09/1.98  --inst_eager_unprocessed_to_passive     true
% 12.09/1.98  --inst_prop_sim_given                   true
% 12.09/1.98  --inst_prop_sim_new                     false
% 12.09/1.98  --inst_subs_new                         false
% 12.09/1.98  --inst_eq_res_simp                      false
% 12.09/1.98  --inst_subs_given                       false
% 12.09/1.98  --inst_orphan_elimination               true
% 12.09/1.98  --inst_learning_loop_flag               true
% 12.09/1.98  --inst_learning_start                   3000
% 12.09/1.98  --inst_learning_factor                  2
% 12.09/1.98  --inst_start_prop_sim_after_learn       3
% 12.09/1.98  --inst_sel_renew                        solver
% 12.09/1.98  --inst_lit_activity_flag                true
% 12.09/1.98  --inst_restr_to_given                   false
% 12.09/1.98  --inst_activity_threshold               500
% 12.09/1.98  --inst_out_proof                        true
% 12.09/1.98  
% 12.09/1.98  ------ Resolution Options
% 12.09/1.98  
% 12.09/1.98  --resolution_flag                       true
% 12.09/1.98  --res_lit_sel                           adaptive
% 12.09/1.98  --res_lit_sel_side                      none
% 12.09/1.98  --res_ordering                          kbo
% 12.09/1.98  --res_to_prop_solver                    active
% 12.09/1.98  --res_prop_simpl_new                    false
% 12.09/1.98  --res_prop_simpl_given                  true
% 12.09/1.98  --res_passive_queue_type                priority_queues
% 12.09/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.09/1.98  --res_passive_queues_freq               [15;5]
% 12.09/1.98  --res_forward_subs                      full
% 12.09/1.98  --res_backward_subs                     full
% 12.09/1.98  --res_forward_subs_resolution           true
% 12.09/1.98  --res_backward_subs_resolution          true
% 12.09/1.98  --res_orphan_elimination                true
% 12.09/1.98  --res_time_limit                        2.
% 12.09/1.98  --res_out_proof                         true
% 12.09/1.98  
% 12.09/1.98  ------ Superposition Options
% 12.09/1.98  
% 12.09/1.98  --superposition_flag                    true
% 12.09/1.98  --sup_passive_queue_type                priority_queues
% 12.09/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.09/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.09/1.98  --demod_completeness_check              fast
% 12.09/1.98  --demod_use_ground                      true
% 12.09/1.98  --sup_to_prop_solver                    passive
% 12.09/1.98  --sup_prop_simpl_new                    true
% 12.09/1.98  --sup_prop_simpl_given                  true
% 12.09/1.98  --sup_fun_splitting                     true
% 12.09/1.98  --sup_smt_interval                      50000
% 12.09/1.98  
% 12.09/1.98  ------ Superposition Simplification Setup
% 12.09/1.98  
% 12.09/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.09/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.09/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.09/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.09/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.09/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.09/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.09/1.98  --sup_immed_triv                        [TrivRules]
% 12.09/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_immed_bw_main                     []
% 12.09/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.09/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.09/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_input_bw                          []
% 12.09/1.98  
% 12.09/1.98  ------ Combination Options
% 12.09/1.98  
% 12.09/1.98  --comb_res_mult                         3
% 12.09/1.98  --comb_sup_mult                         2
% 12.09/1.98  --comb_inst_mult                        10
% 12.09/1.98  
% 12.09/1.98  ------ Debug Options
% 12.09/1.98  
% 12.09/1.98  --dbg_backtrace                         false
% 12.09/1.98  --dbg_dump_prop_clauses                 false
% 12.09/1.98  --dbg_dump_prop_clauses_file            -
% 12.09/1.98  --dbg_out_stat                          false
% 12.09/1.98  ------ Parsing...
% 12.09/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.09/1.98  ------ Proving...
% 12.09/1.98  ------ Problem Properties 
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  clauses                                 46
% 12.09/1.98  conjectures                             11
% 12.09/1.98  EPR                                     9
% 12.09/1.98  Horn                                    42
% 12.09/1.98  unary                                   19
% 12.09/1.98  binary                                  2
% 12.09/1.98  lits                                    162
% 12.09/1.98  lits eq                                 36
% 12.09/1.98  fd_pure                                 0
% 12.09/1.98  fd_pseudo                               0
% 12.09/1.98  fd_cond                                 4
% 12.09/1.98  fd_pseudo_cond                          2
% 12.09/1.98  AC symbols                              0
% 12.09/1.98  
% 12.09/1.98  ------ Schedule dynamic 5 is on 
% 12.09/1.98  
% 12.09/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  ------ 
% 12.09/1.98  Current options:
% 12.09/1.98  ------ 
% 12.09/1.98  
% 12.09/1.98  ------ Input Options
% 12.09/1.98  
% 12.09/1.98  --out_options                           all
% 12.09/1.98  --tptp_safe_out                         true
% 12.09/1.98  --problem_path                          ""
% 12.09/1.98  --include_path                          ""
% 12.09/1.98  --clausifier                            res/vclausify_rel
% 12.09/1.98  --clausifier_options                    ""
% 12.09/1.98  --stdin                                 false
% 12.09/1.98  --stats_out                             all
% 12.09/1.98  
% 12.09/1.98  ------ General Options
% 12.09/1.98  
% 12.09/1.98  --fof                                   false
% 12.09/1.98  --time_out_real                         305.
% 12.09/1.98  --time_out_virtual                      -1.
% 12.09/1.98  --symbol_type_check                     false
% 12.09/1.98  --clausify_out                          false
% 12.09/1.98  --sig_cnt_out                           false
% 12.09/1.98  --trig_cnt_out                          false
% 12.09/1.98  --trig_cnt_out_tolerance                1.
% 12.09/1.98  --trig_cnt_out_sk_spl                   false
% 12.09/1.98  --abstr_cl_out                          false
% 12.09/1.98  
% 12.09/1.98  ------ Global Options
% 12.09/1.98  
% 12.09/1.98  --schedule                              default
% 12.09/1.98  --add_important_lit                     false
% 12.09/1.98  --prop_solver_per_cl                    1000
% 12.09/1.98  --min_unsat_core                        false
% 12.09/1.98  --soft_assumptions                      false
% 12.09/1.98  --soft_lemma_size                       3
% 12.09/1.98  --prop_impl_unit_size                   0
% 12.09/1.98  --prop_impl_unit                        []
% 12.09/1.98  --share_sel_clauses                     true
% 12.09/1.98  --reset_solvers                         false
% 12.09/1.98  --bc_imp_inh                            [conj_cone]
% 12.09/1.98  --conj_cone_tolerance                   3.
% 12.09/1.98  --extra_neg_conj                        none
% 12.09/1.98  --large_theory_mode                     true
% 12.09/1.98  --prolific_symb_bound                   200
% 12.09/1.98  --lt_threshold                          2000
% 12.09/1.98  --clause_weak_htbl                      true
% 12.09/1.98  --gc_record_bc_elim                     false
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing Options
% 12.09/1.98  
% 12.09/1.98  --preprocessing_flag                    true
% 12.09/1.98  --time_out_prep_mult                    0.1
% 12.09/1.98  --splitting_mode                        input
% 12.09/1.98  --splitting_grd                         true
% 12.09/1.98  --splitting_cvd                         false
% 12.09/1.98  --splitting_cvd_svl                     false
% 12.09/1.98  --splitting_nvd                         32
% 12.09/1.98  --sub_typing                            true
% 12.09/1.98  --prep_gs_sim                           true
% 12.09/1.98  --prep_unflatten                        true
% 12.09/1.98  --prep_res_sim                          true
% 12.09/1.98  --prep_upred                            true
% 12.09/1.98  --prep_sem_filter                       exhaustive
% 12.09/1.98  --prep_sem_filter_out                   false
% 12.09/1.98  --pred_elim                             true
% 12.09/1.98  --res_sim_input                         true
% 12.09/1.98  --eq_ax_congr_red                       true
% 12.09/1.98  --pure_diseq_elim                       true
% 12.09/1.98  --brand_transform                       false
% 12.09/1.98  --non_eq_to_eq                          false
% 12.09/1.98  --prep_def_merge                        true
% 12.09/1.98  --prep_def_merge_prop_impl              false
% 12.09/1.98  --prep_def_merge_mbd                    true
% 12.09/1.98  --prep_def_merge_tr_red                 false
% 12.09/1.98  --prep_def_merge_tr_cl                  false
% 12.09/1.98  --smt_preprocessing                     true
% 12.09/1.98  --smt_ac_axioms                         fast
% 12.09/1.98  --preprocessed_out                      false
% 12.09/1.98  --preprocessed_stats                    false
% 12.09/1.98  
% 12.09/1.98  ------ Abstraction refinement Options
% 12.09/1.98  
% 12.09/1.98  --abstr_ref                             []
% 12.09/1.98  --abstr_ref_prep                        false
% 12.09/1.98  --abstr_ref_until_sat                   false
% 12.09/1.98  --abstr_ref_sig_restrict                funpre
% 12.09/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.09/1.98  --abstr_ref_under                       []
% 12.09/1.98  
% 12.09/1.98  ------ SAT Options
% 12.09/1.98  
% 12.09/1.98  --sat_mode                              false
% 12.09/1.98  --sat_fm_restart_options                ""
% 12.09/1.98  --sat_gr_def                            false
% 12.09/1.98  --sat_epr_types                         true
% 12.09/1.98  --sat_non_cyclic_types                  false
% 12.09/1.98  --sat_finite_models                     false
% 12.09/1.98  --sat_fm_lemmas                         false
% 12.09/1.98  --sat_fm_prep                           false
% 12.09/1.98  --sat_fm_uc_incr                        true
% 12.09/1.98  --sat_out_model                         small
% 12.09/1.98  --sat_out_clauses                       false
% 12.09/1.98  
% 12.09/1.98  ------ QBF Options
% 12.09/1.98  
% 12.09/1.98  --qbf_mode                              false
% 12.09/1.98  --qbf_elim_univ                         false
% 12.09/1.98  --qbf_dom_inst                          none
% 12.09/1.98  --qbf_dom_pre_inst                      false
% 12.09/1.98  --qbf_sk_in                             false
% 12.09/1.98  --qbf_pred_elim                         true
% 12.09/1.98  --qbf_split                             512
% 12.09/1.98  
% 12.09/1.98  ------ BMC1 Options
% 12.09/1.98  
% 12.09/1.98  --bmc1_incremental                      false
% 12.09/1.98  --bmc1_axioms                           reachable_all
% 12.09/1.98  --bmc1_min_bound                        0
% 12.09/1.98  --bmc1_max_bound                        -1
% 12.09/1.98  --bmc1_max_bound_default                -1
% 12.09/1.98  --bmc1_symbol_reachability              true
% 12.09/1.98  --bmc1_property_lemmas                  false
% 12.09/1.98  --bmc1_k_induction                      false
% 12.09/1.98  --bmc1_non_equiv_states                 false
% 12.09/1.98  --bmc1_deadlock                         false
% 12.09/1.98  --bmc1_ucm                              false
% 12.09/1.98  --bmc1_add_unsat_core                   none
% 12.09/1.98  --bmc1_unsat_core_children              false
% 12.09/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.09/1.98  --bmc1_out_stat                         full
% 12.09/1.98  --bmc1_ground_init                      false
% 12.09/1.98  --bmc1_pre_inst_next_state              false
% 12.09/1.98  --bmc1_pre_inst_state                   false
% 12.09/1.98  --bmc1_pre_inst_reach_state             false
% 12.09/1.98  --bmc1_out_unsat_core                   false
% 12.09/1.98  --bmc1_aig_witness_out                  false
% 12.09/1.98  --bmc1_verbose                          false
% 12.09/1.98  --bmc1_dump_clauses_tptp                false
% 12.09/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.09/1.98  --bmc1_dump_file                        -
% 12.09/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.09/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.09/1.98  --bmc1_ucm_extend_mode                  1
% 12.09/1.98  --bmc1_ucm_init_mode                    2
% 12.09/1.98  --bmc1_ucm_cone_mode                    none
% 12.09/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.09/1.98  --bmc1_ucm_relax_model                  4
% 12.09/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.09/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.09/1.98  --bmc1_ucm_layered_model                none
% 12.09/1.98  --bmc1_ucm_max_lemma_size               10
% 12.09/1.98  
% 12.09/1.98  ------ AIG Options
% 12.09/1.98  
% 12.09/1.98  --aig_mode                              false
% 12.09/1.98  
% 12.09/1.98  ------ Instantiation Options
% 12.09/1.98  
% 12.09/1.98  --instantiation_flag                    true
% 12.09/1.98  --inst_sos_flag                         true
% 12.09/1.98  --inst_sos_phase                        true
% 12.09/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.09/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.09/1.98  --inst_lit_sel_side                     none
% 12.09/1.98  --inst_solver_per_active                1400
% 12.09/1.98  --inst_solver_calls_frac                1.
% 12.09/1.98  --inst_passive_queue_type               priority_queues
% 12.09/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.09/1.98  --inst_passive_queues_freq              [25;2]
% 12.09/1.98  --inst_dismatching                      true
% 12.09/1.98  --inst_eager_unprocessed_to_passive     true
% 12.09/1.98  --inst_prop_sim_given                   true
% 12.09/1.98  --inst_prop_sim_new                     false
% 12.09/1.98  --inst_subs_new                         false
% 12.09/1.98  --inst_eq_res_simp                      false
% 12.09/1.98  --inst_subs_given                       false
% 12.09/1.98  --inst_orphan_elimination               true
% 12.09/1.98  --inst_learning_loop_flag               true
% 12.09/1.98  --inst_learning_start                   3000
% 12.09/1.98  --inst_learning_factor                  2
% 12.09/1.98  --inst_start_prop_sim_after_learn       3
% 12.09/1.98  --inst_sel_renew                        solver
% 12.09/1.98  --inst_lit_activity_flag                true
% 12.09/1.98  --inst_restr_to_given                   false
% 12.09/1.98  --inst_activity_threshold               500
% 12.09/1.98  --inst_out_proof                        true
% 12.09/1.98  
% 12.09/1.98  ------ Resolution Options
% 12.09/1.98  
% 12.09/1.98  --resolution_flag                       false
% 12.09/1.98  --res_lit_sel                           adaptive
% 12.09/1.98  --res_lit_sel_side                      none
% 12.09/1.98  --res_ordering                          kbo
% 12.09/1.98  --res_to_prop_solver                    active
% 12.09/1.98  --res_prop_simpl_new                    false
% 12.09/1.98  --res_prop_simpl_given                  true
% 12.09/1.98  --res_passive_queue_type                priority_queues
% 12.09/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.09/1.98  --res_passive_queues_freq               [15;5]
% 12.09/1.98  --res_forward_subs                      full
% 12.09/1.98  --res_backward_subs                     full
% 12.09/1.98  --res_forward_subs_resolution           true
% 12.09/1.98  --res_backward_subs_resolution          true
% 12.09/1.98  --res_orphan_elimination                true
% 12.09/1.98  --res_time_limit                        2.
% 12.09/1.98  --res_out_proof                         true
% 12.09/1.98  
% 12.09/1.98  ------ Superposition Options
% 12.09/1.98  
% 12.09/1.98  --superposition_flag                    true
% 12.09/1.98  --sup_passive_queue_type                priority_queues
% 12.09/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.09/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.09/1.98  --demod_completeness_check              fast
% 12.09/1.98  --demod_use_ground                      true
% 12.09/1.98  --sup_to_prop_solver                    passive
% 12.09/1.98  --sup_prop_simpl_new                    true
% 12.09/1.98  --sup_prop_simpl_given                  true
% 12.09/1.98  --sup_fun_splitting                     true
% 12.09/1.98  --sup_smt_interval                      50000
% 12.09/1.98  
% 12.09/1.98  ------ Superposition Simplification Setup
% 12.09/1.98  
% 12.09/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.09/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.09/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.09/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.09/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.09/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.09/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.09/1.98  --sup_immed_triv                        [TrivRules]
% 12.09/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_immed_bw_main                     []
% 12.09/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.09/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.09/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.09/1.98  --sup_input_bw                          []
% 12.09/1.98  
% 12.09/1.98  ------ Combination Options
% 12.09/1.98  
% 12.09/1.98  --comb_res_mult                         3
% 12.09/1.98  --comb_sup_mult                         2
% 12.09/1.98  --comb_inst_mult                        10
% 12.09/1.98  
% 12.09/1.98  ------ Debug Options
% 12.09/1.98  
% 12.09/1.98  --dbg_backtrace                         false
% 12.09/1.98  --dbg_dump_prop_clauses                 false
% 12.09/1.98  --dbg_dump_prop_clauses_file            -
% 12.09/1.98  --dbg_out_stat                          false
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  ------ Proving...
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  % SZS status Theorem for theBenchmark.p
% 12.09/1.98  
% 12.09/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.09/1.98  
% 12.09/1.98  fof(f15,axiom,(
% 12.09/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f42,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 12.09/1.98    inference(ennf_transformation,[],[f15])).
% 12.09/1.98  
% 12.09/1.98  fof(f43,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.09/1.98    inference(flattening,[],[f42])).
% 12.09/1.98  
% 12.09/1.98  fof(f60,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.09/1.98    inference(nnf_transformation,[],[f43])).
% 12.09/1.98  
% 12.09/1.98  fof(f87,plain,(
% 12.09/1.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.09/1.98    inference(cnf_transformation,[],[f60])).
% 12.09/1.98  
% 12.09/1.98  fof(f24,conjecture,(
% 12.09/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f25,negated_conjecture,(
% 12.09/1.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 12.09/1.98    inference(negated_conjecture,[],[f24])).
% 12.09/1.98  
% 12.09/1.98  fof(f56,plain,(
% 12.09/1.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 12.09/1.98    inference(ennf_transformation,[],[f25])).
% 12.09/1.98  
% 12.09/1.98  fof(f57,plain,(
% 12.09/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 12.09/1.98    inference(flattening,[],[f56])).
% 12.09/1.98  
% 12.09/1.98  fof(f62,plain,(
% 12.09/1.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 12.09/1.98    introduced(choice_axiom,[])).
% 12.09/1.98  
% 12.09/1.98  fof(f61,plain,(
% 12.09/1.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 12.09/1.98    introduced(choice_axiom,[])).
% 12.09/1.98  
% 12.09/1.98  fof(f63,plain,(
% 12.09/1.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 12.09/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f62,f61])).
% 12.09/1.98  
% 12.09/1.98  fof(f111,plain,(
% 12.09/1.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f16,axiom,(
% 12.09/1.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f89,plain,(
% 12.09/1.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 12.09/1.98    inference(cnf_transformation,[],[f16])).
% 12.09/1.98  
% 12.09/1.98  fof(f19,axiom,(
% 12.09/1.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f93,plain,(
% 12.09/1.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f19])).
% 12.09/1.98  
% 12.09/1.98  fof(f122,plain,(
% 12.09/1.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 12.09/1.98    inference(definition_unfolding,[],[f89,f93])).
% 12.09/1.98  
% 12.09/1.98  fof(f104,plain,(
% 12.09/1.98    v1_funct_1(sK2)),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f106,plain,(
% 12.09/1.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f107,plain,(
% 12.09/1.98    v1_funct_1(sK3)),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f109,plain,(
% 12.09/1.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f17,axiom,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f44,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 12.09/1.98    inference(ennf_transformation,[],[f17])).
% 12.09/1.98  
% 12.09/1.98  fof(f45,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 12.09/1.98    inference(flattening,[],[f44])).
% 12.09/1.98  
% 12.09/1.98  fof(f91,plain,(
% 12.09/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f45])).
% 12.09/1.98  
% 12.09/1.98  fof(f110,plain,(
% 12.09/1.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f21,axiom,(
% 12.09/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f50,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 12.09/1.98    inference(ennf_transformation,[],[f21])).
% 12.09/1.98  
% 12.09/1.98  fof(f51,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 12.09/1.98    inference(flattening,[],[f50])).
% 12.09/1.98  
% 12.09/1.98  fof(f97,plain,(
% 12.09/1.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f51])).
% 12.09/1.98  
% 12.09/1.98  fof(f105,plain,(
% 12.09/1.98    v1_funct_2(sK2,sK0,sK1)),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f108,plain,(
% 12.09/1.98    v1_funct_2(sK3,sK1,sK0)),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f113,plain,(
% 12.09/1.98    k1_xboole_0 != sK0),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  fof(f1,axiom,(
% 12.09/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f58,plain,(
% 12.09/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.09/1.98    inference(nnf_transformation,[],[f1])).
% 12.09/1.98  
% 12.09/1.98  fof(f59,plain,(
% 12.09/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.09/1.98    inference(flattening,[],[f58])).
% 12.09/1.98  
% 12.09/1.98  fof(f64,plain,(
% 12.09/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.09/1.98    inference(cnf_transformation,[],[f59])).
% 12.09/1.98  
% 12.09/1.98  fof(f124,plain,(
% 12.09/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.09/1.98    inference(equality_resolution,[],[f64])).
% 12.09/1.98  
% 12.09/1.98  fof(f66,plain,(
% 12.09/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f59])).
% 12.09/1.98  
% 12.09/1.98  fof(f7,axiom,(
% 12.09/1.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f75,plain,(
% 12.09/1.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 12.09/1.98    inference(cnf_transformation,[],[f7])).
% 12.09/1.98  
% 12.09/1.98  fof(f119,plain,(
% 12.09/1.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 12.09/1.98    inference(definition_unfolding,[],[f75,f93])).
% 12.09/1.98  
% 12.09/1.98  fof(f9,axiom,(
% 12.09/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f33,plain,(
% 12.09/1.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 12.09/1.98    inference(ennf_transformation,[],[f9])).
% 12.09/1.98  
% 12.09/1.98  fof(f34,plain,(
% 12.09/1.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 12.09/1.98    inference(flattening,[],[f33])).
% 12.09/1.98  
% 12.09/1.98  fof(f79,plain,(
% 12.09/1.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f34])).
% 12.09/1.98  
% 12.09/1.98  fof(f14,axiom,(
% 12.09/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f41,plain,(
% 12.09/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.09/1.98    inference(ennf_transformation,[],[f14])).
% 12.09/1.98  
% 12.09/1.98  fof(f86,plain,(
% 12.09/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.09/1.98    inference(cnf_transformation,[],[f41])).
% 12.09/1.98  
% 12.09/1.98  fof(f20,axiom,(
% 12.09/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f48,plain,(
% 12.09/1.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 12.09/1.98    inference(ennf_transformation,[],[f20])).
% 12.09/1.98  
% 12.09/1.98  fof(f49,plain,(
% 12.09/1.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 12.09/1.98    inference(flattening,[],[f48])).
% 12.09/1.98  
% 12.09/1.98  fof(f94,plain,(
% 12.09/1.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f49])).
% 12.09/1.98  
% 12.09/1.98  fof(f2,axiom,(
% 12.09/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f26,plain,(
% 12.09/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 12.09/1.98    inference(ennf_transformation,[],[f2])).
% 12.09/1.98  
% 12.09/1.98  fof(f67,plain,(
% 12.09/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f26])).
% 12.09/1.98  
% 12.09/1.98  fof(f3,axiom,(
% 12.09/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f68,plain,(
% 12.09/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 12.09/1.98    inference(cnf_transformation,[],[f3])).
% 12.09/1.98  
% 12.09/1.98  fof(f18,axiom,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f46,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 12.09/1.98    inference(ennf_transformation,[],[f18])).
% 12.09/1.98  
% 12.09/1.98  fof(f47,plain,(
% 12.09/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 12.09/1.98    inference(flattening,[],[f46])).
% 12.09/1.98  
% 12.09/1.98  fof(f92,plain,(
% 12.09/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f47])).
% 12.09/1.98  
% 12.09/1.98  fof(f5,axiom,(
% 12.09/1.98    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(X1,X2) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f27,plain,(
% 12.09/1.98    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 12.09/1.98    inference(ennf_transformation,[],[f5])).
% 12.09/1.98  
% 12.09/1.98  fof(f28,plain,(
% 12.09/1.98    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 12.09/1.98    inference(flattening,[],[f27])).
% 12.09/1.98  
% 12.09/1.98  fof(f71,plain,(
% 12.09/1.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k6_relat_1(k1_relat_1(X3)) != k5_relat_1(X1,X2) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f28])).
% 12.09/1.98  
% 12.09/1.98  fof(f118,plain,(
% 12.09/1.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 12.09/1.98    inference(definition_unfolding,[],[f71,f93,f93])).
% 12.09/1.98  
% 12.09/1.98  fof(f22,axiom,(
% 12.09/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f52,plain,(
% 12.09/1.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 12.09/1.98    inference(ennf_transformation,[],[f22])).
% 12.09/1.98  
% 12.09/1.98  fof(f53,plain,(
% 12.09/1.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 12.09/1.98    inference(flattening,[],[f52])).
% 12.09/1.98  
% 12.09/1.98  fof(f99,plain,(
% 12.09/1.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f53])).
% 12.09/1.98  
% 12.09/1.98  fof(f6,axiom,(
% 12.09/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f29,plain,(
% 12.09/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 12.09/1.98    inference(ennf_transformation,[],[f6])).
% 12.09/1.98  
% 12.09/1.98  fof(f30,plain,(
% 12.09/1.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 12.09/1.98    inference(flattening,[],[f29])).
% 12.09/1.98  
% 12.09/1.98  fof(f72,plain,(
% 12.09/1.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f30])).
% 12.09/1.98  
% 12.09/1.98  fof(f11,axiom,(
% 12.09/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 12.09/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.09/1.98  
% 12.09/1.98  fof(f37,plain,(
% 12.09/1.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 12.09/1.98    inference(ennf_transformation,[],[f11])).
% 12.09/1.98  
% 12.09/1.98  fof(f38,plain,(
% 12.09/1.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 12.09/1.98    inference(flattening,[],[f37])).
% 12.09/1.98  
% 12.09/1.98  fof(f83,plain,(
% 12.09/1.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 12.09/1.98    inference(cnf_transformation,[],[f38])).
% 12.09/1.98  
% 12.09/1.98  fof(f115,plain,(
% 12.09/1.98    k2_funct_1(sK2) != sK3),
% 12.09/1.98    inference(cnf_transformation,[],[f63])).
% 12.09/1.98  
% 12.09/1.98  cnf(c_854,plain,
% 12.09/1.98      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 12.09/1.98      theory(equality) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_39805,plain,
% 12.09/1.98      ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 12.09/1.98      | sK2 != k2_funct_1(sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_854]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_844,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3244,plain,
% 12.09/1.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_844]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_7587,plain,
% 12.09/1.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_3244]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_19732,plain,
% 12.09/1.98      ( k2_funct_1(sK3) != sK2 | sK2 = k2_funct_1(sK3) | sK2 != sK2 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_7587]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1560,plain,
% 12.09/1.98      ( k2_funct_1(sK2) != X0 | k2_funct_1(sK2) = sK3 | sK3 != X0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_844]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_18639,plain,
% 12.09/1.98      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 12.09/1.98      | k2_funct_1(sK2) = sK3
% 12.09/1.98      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1560]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_24,plain,
% 12.09/1.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 12.09/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.09/1.98      | X2 = X3 ),
% 12.09/1.98      inference(cnf_transformation,[],[f87]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_43,negated_conjecture,
% 12.09/1.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 12.09/1.98      inference(cnf_transformation,[],[f111]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_517,plain,
% 12.09/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | X0 = X3
% 12.09/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
% 12.09/1.98      | k6_partfun1(sK0) != X0
% 12.09/1.98      | sK0 != X2
% 12.09/1.98      | sK0 != X1 ),
% 12.09/1.98      inference(resolution_lifted,[status(thm)],[c_24,c_43]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_518,plain,
% 12.09/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 12.09/1.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 12.09/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 12.09/1.98      inference(unflattening,[status(thm)],[c_517]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_25,plain,
% 12.09/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 12.09/1.98      inference(cnf_transformation,[],[f122]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_526,plain,
% 12.09/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 12.09/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 12.09/1.98      inference(forward_subsumption_resolution,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_518,c_25]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1470,plain,
% 12.09/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 12.09/1.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_50,negated_conjecture,
% 12.09/1.98      ( v1_funct_1(sK2) ),
% 12.09/1.98      inference(cnf_transformation,[],[f104]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_48,negated_conjecture,
% 12.09/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 12.09/1.98      inference(cnf_transformation,[],[f106]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_47,negated_conjecture,
% 12.09/1.98      ( v1_funct_1(sK3) ),
% 12.09/1.98      inference(cnf_transformation,[],[f107]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_45,negated_conjecture,
% 12.09/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 12.09/1.98      inference(cnf_transformation,[],[f109]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_26,plain,
% 12.09/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 12.09/1.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X3) ),
% 12.09/1.98      inference(cnf_transformation,[],[f91]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1938,plain,
% 12.09/1.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 12.09/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 12.09/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 12.09/1.98      | ~ v1_funct_1(sK3)
% 12.09/1.98      | ~ v1_funct_1(sK2) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_26]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2592,plain,
% 12.09/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_1470,c_50,c_48,c_47,c_45,c_526,c_1938]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_44,negated_conjecture,
% 12.09/1.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 12.09/1.98      inference(cnf_transformation,[],[f110]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_31,plain,
% 12.09/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 12.09/1.98      | ~ v1_funct_2(X3,X2,X4)
% 12.09/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 12.09/1.98      | v2_funct_1(X3)
% 12.09/1.98      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 12.09/1.98      | ~ v1_funct_1(X3)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | k2_relset_1(X1,X2,X0) != X2
% 12.09/1.98      | k1_xboole_0 = X4 ),
% 12.09/1.98      inference(cnf_transformation,[],[f97]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1485,plain,
% 12.09/1.98      ( k2_relset_1(X0,X1,X2) != X1
% 12.09/1.98      | k1_xboole_0 = X3
% 12.09/1.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 12.09/1.98      | v1_funct_2(X4,X1,X3) != iProver_top
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 12.09/1.98      | v2_funct_1(X4) = iProver_top
% 12.09/1.98      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 12.09/1.98      | v1_funct_1(X2) != iProver_top
% 12.09/1.98      | v1_funct_1(X4) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9055,plain,
% 12.09/1.98      ( k1_xboole_0 = X0
% 12.09/1.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 12.09/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 12.09/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 12.09/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 12.09/1.98      | v2_funct_1(X1) = iProver_top
% 12.09/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 12.09/1.98      | v1_funct_1(X1) != iProver_top
% 12.09/1.98      | v1_funct_1(sK2) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_44,c_1485]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_51,plain,
% 12.09/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_49,negated_conjecture,
% 12.09/1.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 12.09/1.98      inference(cnf_transformation,[],[f105]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_52,plain,
% 12.09/1.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_53,plain,
% 12.09/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9280,plain,
% 12.09/1.98      ( v1_funct_1(X1) != iProver_top
% 12.09/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 12.09/1.98      | v2_funct_1(X1) = iProver_top
% 12.09/1.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 12.09/1.98      | k1_xboole_0 = X0
% 12.09/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_9055,c_51,c_52,c_53]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9281,plain,
% 12.09/1.98      ( k1_xboole_0 = X0
% 12.09/1.98      | v1_funct_2(X1,sK1,X0) != iProver_top
% 12.09/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 12.09/1.98      | v2_funct_1(X1) = iProver_top
% 12.09/1.98      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 12.09/1.98      | v1_funct_1(X1) != iProver_top ),
% 12.09/1.98      inference(renaming,[status(thm)],[c_9280]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9284,plain,
% 12.09/1.98      ( sK0 = k1_xboole_0
% 12.09/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 12.09/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 12.09/1.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 12.09/1.98      | v2_funct_1(sK3) = iProver_top
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_2592,c_9281]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_54,plain,
% 12.09/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_46,negated_conjecture,
% 12.09/1.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f108]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_55,plain,
% 12.09/1.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_56,plain,
% 12.09/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_41,negated_conjecture,
% 12.09/1.98      ( k1_xboole_0 != sK0 ),
% 12.09/1.98      inference(cnf_transformation,[],[f113]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2,plain,
% 12.09/1.98      ( r1_tarski(X0,X0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f124]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_154,plain,
% 12.09/1.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_0,plain,
% 12.09/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 12.09/1.98      inference(cnf_transformation,[],[f66]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_158,plain,
% 12.09/1.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 12.09/1.98      | k1_xboole_0 = k1_xboole_0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1598,plain,
% 12.09/1.98      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_844]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1599,plain,
% 12.09/1.98      ( sK0 != k1_xboole_0
% 12.09/1.98      | k1_xboole_0 = sK0
% 12.09/1.98      | k1_xboole_0 != k1_xboole_0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1598]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_10,plain,
% 12.09/1.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 12.09/1.98      inference(cnf_transformation,[],[f119]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3229,plain,
% 12.09/1.98      ( v2_funct_1(k6_partfun1(sK0)) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3230,plain,
% 12.09/1.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_3229]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9613,plain,
% 12.09/1.98      ( v2_funct_1(sK3) = iProver_top ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_9284,c_54,c_55,c_56,c_41,c_154,c_158,c_1599,c_3230]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_16,plain,
% 12.09/1.98      ( ~ v2_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_relat_1(X0)
% 12.09/1.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f79]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1496,plain,
% 12.09/1.98      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 12.09/1.98      | v2_funct_1(X0) != iProver_top
% 12.09/1.98      | v1_funct_1(X0) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9622,plain,
% 12.09/1.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_9613,c_1496]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1477,plain,
% 12.09/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_22,plain,
% 12.09/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f86]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1491,plain,
% 12.09/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3025,plain,
% 12.09/1.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1477,c_1491]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_29,plain,
% 12.09/1.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 12.09/1.98      | ~ v1_funct_2(X2,X0,X1)
% 12.09/1.98      | ~ v1_funct_2(X3,X1,X0)
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 12.09/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.09/1.98      | ~ v1_funct_1(X3)
% 12.09/1.98      | ~ v1_funct_1(X2)
% 12.09/1.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 12.09/1.98      inference(cnf_transformation,[],[f94]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_530,plain,
% 12.09/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 12.09/1.98      | ~ v1_funct_2(X3,X2,X1)
% 12.09/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 12.09/1.98      | ~ v1_funct_1(X3)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 12.09/1.98      | k2_relset_1(X2,X1,X3) = X1
% 12.09/1.98      | k6_partfun1(X1) != k6_partfun1(sK0)
% 12.09/1.98      | sK0 != X1 ),
% 12.09/1.98      inference(resolution_lifted,[status(thm)],[c_29,c_43]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_531,plain,
% 12.09/1.98      ( ~ v1_funct_2(X0,X1,sK0)
% 12.09/1.98      | ~ v1_funct_2(X2,sK0,X1)
% 12.09/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 12.09/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 12.09/1.98      | ~ v1_funct_1(X2)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 12.09/1.98      | k2_relset_1(X1,sK0,X0) = sK0
% 12.09/1.98      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 12.09/1.98      inference(unflattening,[status(thm)],[c_530]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_624,plain,
% 12.09/1.98      ( ~ v1_funct_2(X0,X1,sK0)
% 12.09/1.98      | ~ v1_funct_2(X2,sK0,X1)
% 12.09/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 12.09/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X2)
% 12.09/1.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 12.09/1.98      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 12.09/1.98      inference(equality_resolution_simp,[status(thm)],[c_531]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1469,plain,
% 12.09/1.98      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 12.09/1.98      | k2_relset_1(X0,sK0,X2) = sK0
% 12.09/1.98      | v1_funct_2(X2,X0,sK0) != iProver_top
% 12.09/1.98      | v1_funct_2(X1,sK0,X0) != iProver_top
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 12.09/1.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 12.09/1.98      | v1_funct_1(X2) != iProver_top
% 12.09/1.98      | v1_funct_1(X1) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2084,plain,
% 12.09/1.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 12.09/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 12.09/1.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 12.09/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 12.09/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_funct_1(sK2) != iProver_top ),
% 12.09/1.98      inference(equality_resolution,[status(thm)],[c_1469]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2599,plain,
% 12.09/1.98      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_2084,c_51,c_52,c_53,c_54,c_55,c_56]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3028,plain,
% 12.09/1.98      ( k2_relat_1(sK3) = sK0 ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_3025,c_2599]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9625,plain,
% 12.09/1.98      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_9622,c_3028]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3,plain,
% 12.09/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.09/1.98      | ~ v1_relat_1(X1)
% 12.09/1.98      | v1_relat_1(X0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f67]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1687,plain,
% 12.09/1.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 12.09/1.98      | ~ v1_relat_1(X0)
% 12.09/1.98      | v1_relat_1(sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1962,plain,
% 12.09/1.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 12.09/1.98      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 12.09/1.98      | v1_relat_1(sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1687]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2691,plain,
% 12.09/1.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 12.09/1.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 12.09/1.98      | v1_relat_1(sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1962]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2692,plain,
% 12.09/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 12.09/1.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_2691]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_4,plain,
% 12.09/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 12.09/1.98      inference(cnf_transformation,[],[f68]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2989,plain,
% 12.09/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_4]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2990,plain,
% 12.09/1.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_2989]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17200,plain,
% 12.09/1.98      ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_9625,c_54,c_56,c_2692,c_2990]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1474,plain,
% 12.09/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_28,plain,
% 12.09/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X3)
% 12.09/1.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 12.09/1.98      inference(cnf_transformation,[],[f92]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1487,plain,
% 12.09/1.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 12.09/1.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 12.09/1.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | v1_funct_1(X5) != iProver_top
% 12.09/1.98      | v1_funct_1(X4) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_6037,plain,
% 12.09/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | v1_funct_1(X2) != iProver_top
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1477,c_1487]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_6203,plain,
% 12.09/1.98      ( v1_funct_1(X2) != iProver_top
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_6037,c_54]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_6204,plain,
% 12.09/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | v1_funct_1(X2) != iProver_top ),
% 12.09/1.98      inference(renaming,[status(thm)],[c_6203]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_6213,plain,
% 12.09/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 12.09/1.98      | v1_funct_1(sK2) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1474,c_6204]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_6216,plain,
% 12.09/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 12.09/1.98      | v1_funct_1(sK2) != iProver_top ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_6213,c_2592]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_7632,plain,
% 12.09/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_6216,c_51]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_7,plain,
% 12.09/1.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 12.09/1.98      | ~ v1_relat_1(X0)
% 12.09/1.98      | ~ v1_relat_1(X2)
% 12.09/1.98      | ~ v1_relat_1(X3)
% 12.09/1.98      | X2 = X0
% 12.09/1.98      | k5_relat_1(X3,X2) != k6_partfun1(X1)
% 12.09/1.98      | k5_relat_1(X0,X3) != k6_partfun1(k1_relat_1(X2)) ),
% 12.09/1.98      inference(cnf_transformation,[],[f118]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1503,plain,
% 12.09/1.98      ( X0 = X1
% 12.09/1.98      | k5_relat_1(X2,X0) != k6_partfun1(X3)
% 12.09/1.98      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 12.09/1.98      | r1_tarski(k2_relat_1(X1),X3) != iProver_top
% 12.09/1.98      | v1_relat_1(X1) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) != iProver_top
% 12.09/1.98      | v1_relat_1(X2) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_7634,plain,
% 12.09/1.98      ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
% 12.09/1.98      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
% 12.09/1.98      | sK2 = X0
% 12.09/1.98      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(sK2) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_7632,c_1503]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3026,plain,
% 12.09/1.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1474,c_1491]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3027,plain,
% 12.09/1.98      ( k2_relat_1(sK2) = sK1 ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_3026,c_44]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_7635,plain,
% 12.09/1.98      ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
% 12.09/1.98      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
% 12.09/1.98      | sK2 = X0
% 12.09/1.98      | r1_tarski(sK1,X1) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(sK2) != iProver_top ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_7634,c_3027]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1504,plain,
% 12.09/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1505,plain,
% 12.09/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.09/1.98      | v1_relat_1(X1) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3167,plain,
% 12.09/1.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 12.09/1.98      | v1_relat_1(sK2) = iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1474,c_1505]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3331,plain,
% 12.09/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_1504,c_3167]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_8334,plain,
% 12.09/1.98      ( k5_relat_1(sK3,X0) != k6_partfun1(X1)
% 12.09/1.98      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK0)
% 12.09/1.98      | sK2 = X0
% 12.09/1.98      | r1_tarski(sK1,X1) != iProver_top
% 12.09/1.98      | v1_relat_1(X0) != iProver_top ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_7635,c_56,c_2692,c_2990,c_3331]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17213,plain,
% 12.09/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_partfun1(X0)
% 12.09/1.98      | k2_funct_1(sK3) = sK2
% 12.09/1.98      | r1_tarski(sK1,X0) != iProver_top
% 12.09/1.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_17200,c_8334]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_35,plain,
% 12.09/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 12.09/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 12.09/1.98      | ~ v2_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | k2_relset_1(X1,X2,X0) != X2
% 12.09/1.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 12.09/1.98      | k1_xboole_0 = X2 ),
% 12.09/1.98      inference(cnf_transformation,[],[f99]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1481,plain,
% 12.09/1.98      ( k2_relset_1(X0,X1,X2) != X1
% 12.09/1.98      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 12.09/1.98      | k1_xboole_0 = X1
% 12.09/1.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 12.09/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 12.09/1.98      | v2_funct_1(X2) != iProver_top
% 12.09/1.98      | v1_funct_1(X2) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3548,plain,
% 12.09/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 12.09/1.98      | sK0 = k1_xboole_0
% 12.09/1.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 12.09/1.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 12.09/1.98      | v2_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_2599,c_1481]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_5799,plain,
% 12.09/1.98      ( v2_funct_1(sK3) != iProver_top
% 12.09/1.98      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_3548,c_54,c_55,c_56,c_41,c_154,c_158,c_1599]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_5800,plain,
% 12.09/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 12.09/1.98      | v2_funct_1(sK3) != iProver_top ),
% 12.09/1.98      inference(renaming,[status(thm)],[c_5799]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9624,plain,
% 12.09/1.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 12.09/1.98      inference(superposition,[status(thm)],[c_9613,c_5800]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17219,plain,
% 12.09/1.98      ( k2_funct_1(sK3) = sK2
% 12.09/1.98      | k6_partfun1(X0) != k6_partfun1(sK1)
% 12.09/1.98      | r1_tarski(sK1,X0) != iProver_top
% 12.09/1.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 12.09/1.98      inference(light_normalisation,[status(thm)],[c_17213,c_9624]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_9,plain,
% 12.09/1.98      ( ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_relat_1(X0)
% 12.09/1.98      | v1_relat_1(k2_funct_1(X0)) ),
% 12.09/1.98      inference(cnf_transformation,[],[f72]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3065,plain,
% 12.09/1.98      ( ~ v1_funct_1(sK3)
% 12.09/1.98      | v1_relat_1(k2_funct_1(sK3))
% 12.09/1.98      | ~ v1_relat_1(sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3066,plain,
% 12.09/1.98      ( v1_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_3065]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17703,plain,
% 12.09/1.98      ( r1_tarski(sK1,X0) != iProver_top
% 12.09/1.98      | k6_partfun1(X0) != k6_partfun1(sK1)
% 12.09/1.98      | k2_funct_1(sK3) = sK2 ),
% 12.09/1.98      inference(global_propositional_subsumption,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_17219,c_54,c_56,c_2692,c_2990,c_3066]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17704,plain,
% 12.09/1.98      ( k2_funct_1(sK3) = sK2
% 12.09/1.98      | k6_partfun1(X0) != k6_partfun1(sK1)
% 12.09/1.98      | r1_tarski(sK1,X0) != iProver_top ),
% 12.09/1.98      inference(renaming,[status(thm)],[c_17703]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_17709,plain,
% 12.09/1.98      ( k2_funct_1(sK3) = sK2 | r1_tarski(sK1,sK1) != iProver_top ),
% 12.09/1.98      inference(equality_resolution,[status(thm)],[c_17704]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_19,plain,
% 12.09/1.98      ( ~ v2_funct_1(X0)
% 12.09/1.98      | ~ v1_funct_1(X0)
% 12.09/1.98      | ~ v1_relat_1(X0)
% 12.09/1.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 12.09/1.98      inference(cnf_transformation,[],[f83]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_4336,plain,
% 12.09/1.98      ( ~ v2_funct_1(sK3)
% 12.09/1.98      | ~ v1_funct_1(sK3)
% 12.09/1.98      | ~ v1_relat_1(sK3)
% 12.09/1.98      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_19]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_4337,plain,
% 12.09/1.98      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 12.09/1.98      | v2_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_funct_1(sK3) != iProver_top
% 12.09/1.98      | v1_relat_1(sK3) != iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_4336]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_4207,plain,
% 12.09/1.98      ( r1_tarski(sK2,sK2) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1657,plain,
% 12.09/1.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_844]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2073,plain,
% 12.09/1.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1657]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3482,plain,
% 12.09/1.98      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 12.09/1.98      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 12.09/1.98      | sK3 != sK3 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2073]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2190,plain,
% 12.09/1.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_3232,plain,
% 12.09/1.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2190]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2605,plain,
% 12.09/1.98      ( r1_tarski(sK1,sK1) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2606,plain,
% 12.09/1.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 12.09/1.98      inference(predicate_to_equality,[status(thm)],[c_2605]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2601,plain,
% 12.09/1.98      ( r1_tarski(sK3,sK3) ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_1651,plain,
% 12.09/1.98      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_0]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_2054,plain,
% 12.09/1.98      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 12.09/1.98      inference(instantiation,[status(thm)],[c_1651]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(c_39,negated_conjecture,
% 12.09/1.98      ( k2_funct_1(sK2) != sK3 ),
% 12.09/1.98      inference(cnf_transformation,[],[f115]) ).
% 12.09/1.98  
% 12.09/1.98  cnf(contradiction,plain,
% 12.09/1.98      ( $false ),
% 12.09/1.98      inference(minisat,
% 12.09/1.98                [status(thm)],
% 12.09/1.98                [c_39805,c_19732,c_18639,c_17709,c_9284,c_4337,c_4207,
% 12.09/1.98                 c_3482,c_3232,c_3230,c_2990,c_2692,c_2606,c_2601,c_2054,
% 12.09/1.98                 c_1599,c_158,c_154,c_39,c_41,c_56,c_55,c_54]) ).
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 12.09/1.98  
% 12.09/1.98  ------                               Statistics
% 12.09/1.98  
% 12.09/1.98  ------ General
% 12.09/1.98  
% 12.09/1.98  abstr_ref_over_cycles:                  0
% 12.09/1.98  abstr_ref_under_cycles:                 0
% 12.09/1.98  gc_basic_clause_elim:                   0
% 12.09/1.98  forced_gc_time:                         0
% 12.09/1.98  parsing_time:                           0.01
% 12.09/1.98  unif_index_cands_time:                  0.
% 12.09/1.98  unif_index_add_time:                    0.
% 12.09/1.98  orderings_time:                         0.
% 12.09/1.98  out_proof_time:                         0.018
% 12.09/1.98  total_time:                             1.488
% 12.09/1.98  num_of_symbols:                         52
% 12.09/1.98  num_of_terms:                           52485
% 12.09/1.98  
% 12.09/1.98  ------ Preprocessing
% 12.09/1.98  
% 12.09/1.98  num_of_splits:                          0
% 12.09/1.98  num_of_split_atoms:                     0
% 12.09/1.98  num_of_reused_defs:                     0
% 12.09/1.98  num_eq_ax_congr_red:                    3
% 12.09/1.98  num_of_sem_filtered_clauses:            1
% 12.09/1.98  num_of_subtypes:                        0
% 12.09/1.98  monotx_restored_types:                  0
% 12.09/1.98  sat_num_of_epr_types:                   0
% 12.09/1.98  sat_num_of_non_cyclic_types:            0
% 12.09/1.98  sat_guarded_non_collapsed_types:        0
% 12.09/1.98  num_pure_diseq_elim:                    0
% 12.09/1.98  simp_replaced_by:                       0
% 12.09/1.98  res_preprocessed:                       220
% 12.09/1.98  prep_upred:                             0
% 12.09/1.98  prep_unflattend:                        12
% 12.09/1.98  smt_new_axioms:                         0
% 12.09/1.98  pred_elim_cands:                        6
% 12.09/1.98  pred_elim:                              1
% 12.09/1.98  pred_elim_cl:                           1
% 12.09/1.98  pred_elim_cycles:                       3
% 12.09/1.98  merged_defs:                            0
% 12.09/1.98  merged_defs_ncl:                        0
% 12.09/1.98  bin_hyper_res:                          0
% 12.09/1.98  prep_cycles:                            4
% 12.09/1.98  pred_elim_time:                         0.005
% 12.09/1.98  splitting_time:                         0.
% 12.09/1.98  sem_filter_time:                        0.
% 12.09/1.98  monotx_time:                            0.001
% 12.09/1.98  subtype_inf_time:                       0.
% 12.09/1.98  
% 12.09/1.98  ------ Problem properties
% 12.09/1.98  
% 12.09/1.98  clauses:                                46
% 12.09/1.98  conjectures:                            11
% 12.09/1.98  epr:                                    9
% 12.09/1.98  horn:                                   42
% 12.09/1.98  ground:                                 12
% 12.09/1.98  unary:                                  19
% 12.09/1.98  binary:                                 2
% 12.09/1.98  lits:                                   162
% 12.09/1.98  lits_eq:                                36
% 12.09/1.98  fd_pure:                                0
% 12.09/1.98  fd_pseudo:                              0
% 12.09/1.98  fd_cond:                                4
% 12.09/1.98  fd_pseudo_cond:                         2
% 12.09/1.98  ac_symbols:                             0
% 12.09/1.98  
% 12.09/1.98  ------ Propositional Solver
% 12.09/1.98  
% 12.09/1.98  prop_solver_calls:                      34
% 12.09/1.98  prop_fast_solver_calls:                 3440
% 12.09/1.98  smt_solver_calls:                       0
% 12.09/1.98  smt_fast_solver_calls:                  0
% 12.09/1.98  prop_num_of_clauses:                    20050
% 12.09/1.98  prop_preprocess_simplified:             39886
% 12.09/1.98  prop_fo_subsumed:                       495
% 12.09/1.98  prop_solver_time:                       0.
% 12.09/1.98  smt_solver_time:                        0.
% 12.09/1.98  smt_fast_solver_time:                   0.
% 12.09/1.98  prop_fast_solver_time:                  0.
% 12.09/1.98  prop_unsat_core_time:                   0.002
% 12.09/1.98  
% 12.09/1.98  ------ QBF
% 12.09/1.98  
% 12.09/1.98  qbf_q_res:                              0
% 12.09/1.98  qbf_num_tautologies:                    0
% 12.09/1.98  qbf_prep_cycles:                        0
% 12.09/1.98  
% 12.09/1.98  ------ BMC1
% 12.09/1.98  
% 12.09/1.98  bmc1_current_bound:                     -1
% 12.09/1.98  bmc1_last_solved_bound:                 -1
% 12.09/1.98  bmc1_unsat_core_size:                   -1
% 12.09/1.98  bmc1_unsat_core_parents_size:           -1
% 12.09/1.98  bmc1_merge_next_fun:                    0
% 12.09/1.98  bmc1_unsat_core_clauses_time:           0.
% 12.09/1.98  
% 12.09/1.98  ------ Instantiation
% 12.09/1.98  
% 12.09/1.98  inst_num_of_clauses:                    4564
% 12.09/1.98  inst_num_in_passive:                    2391
% 12.09/1.98  inst_num_in_active:                     1960
% 12.09/1.98  inst_num_in_unprocessed:                212
% 12.09/1.98  inst_num_of_loops:                      2128
% 12.09/1.98  inst_num_of_learning_restarts:          0
% 12.09/1.98  inst_num_moves_active_passive:          166
% 12.09/1.98  inst_lit_activity:                      0
% 12.09/1.98  inst_lit_activity_moves:                3
% 12.09/1.98  inst_num_tautologies:                   0
% 12.09/1.98  inst_num_prop_implied:                  0
% 12.09/1.98  inst_num_existing_simplified:           0
% 12.09/1.98  inst_num_eq_res_simplified:             0
% 12.09/1.98  inst_num_child_elim:                    0
% 12.09/1.98  inst_num_of_dismatching_blockings:      1991
% 12.09/1.98  inst_num_of_non_proper_insts:           5097
% 12.09/1.98  inst_num_of_duplicates:                 0
% 12.09/1.98  inst_inst_num_from_inst_to_res:         0
% 12.09/1.98  inst_dismatching_checking_time:         0.
% 12.09/1.98  
% 12.09/1.98  ------ Resolution
% 12.09/1.98  
% 12.09/1.98  res_num_of_clauses:                     0
% 12.09/1.98  res_num_in_passive:                     0
% 12.09/1.98  res_num_in_active:                      0
% 12.09/1.98  res_num_of_loops:                       224
% 12.09/1.98  res_forward_subset_subsumed:            193
% 12.09/1.98  res_backward_subset_subsumed:           0
% 12.09/1.98  res_forward_subsumed:                   0
% 12.09/1.98  res_backward_subsumed:                  0
% 12.09/1.98  res_forward_subsumption_resolution:     2
% 12.09/1.98  res_backward_subsumption_resolution:    0
% 12.09/1.98  res_clause_to_clause_subsumption:       2649
% 12.09/1.98  res_orphan_elimination:                 0
% 12.09/1.98  res_tautology_del:                      78
% 12.09/1.98  res_num_eq_res_simplified:              1
% 12.09/1.98  res_num_sel_changes:                    0
% 12.09/1.98  res_moves_from_active_to_pass:          0
% 12.09/1.98  
% 12.09/1.98  ------ Superposition
% 12.09/1.98  
% 12.09/1.98  sup_time_total:                         0.
% 12.09/1.98  sup_time_generating:                    0.
% 12.09/1.98  sup_time_sim_full:                      0.
% 12.09/1.98  sup_time_sim_immed:                     0.
% 12.09/1.98  
% 12.09/1.98  sup_num_of_clauses:                     1308
% 12.09/1.98  sup_num_in_active:                      380
% 12.09/1.98  sup_num_in_passive:                     928
% 12.09/1.98  sup_num_of_loops:                       424
% 12.09/1.98  sup_fw_superposition:                   762
% 12.09/1.98  sup_bw_superposition:                   803
% 12.09/1.98  sup_immediate_simplified:               457
% 12.09/1.98  sup_given_eliminated:                   0
% 12.09/1.98  comparisons_done:                       0
% 12.09/1.98  comparisons_avoided:                    2
% 12.09/1.98  
% 12.09/1.98  ------ Simplifications
% 12.09/1.98  
% 12.09/1.98  
% 12.09/1.98  sim_fw_subset_subsumed:                 51
% 12.09/1.98  sim_bw_subset_subsumed:                 39
% 12.09/1.98  sim_fw_subsumed:                        31
% 12.09/1.98  sim_bw_subsumed:                        6
% 12.09/1.98  sim_fw_subsumption_res:                 0
% 12.09/1.98  sim_bw_subsumption_res:                 0
% 12.09/1.98  sim_tautology_del:                      8
% 12.09/1.98  sim_eq_tautology_del:                   136
% 12.09/1.98  sim_eq_res_simp:                        3
% 12.09/1.98  sim_fw_demodulated:                     70
% 12.09/1.98  sim_bw_demodulated:                     23
% 12.09/1.98  sim_light_normalised:                   356
% 12.09/1.98  sim_joinable_taut:                      0
% 12.09/1.98  sim_joinable_simp:                      0
% 12.09/1.98  sim_ac_normalised:                      0
% 12.09/1.98  sim_smt_subsumption:                    0
% 12.09/1.98  
%------------------------------------------------------------------------------
