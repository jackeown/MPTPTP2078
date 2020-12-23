%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:00 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 810 expanded)
%              Number of clauses        :  102 ( 250 expanded)
%              Number of leaves         :   21 ( 197 expanded)
%              Depth                    :   21
%              Number of atoms          :  592 (5092 expanded)
%              Number of equality atoms :  216 ( 461 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f44,f43])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f67])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1435,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_522,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_530,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_522,c_20])).

cnf(c_1421,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_3757,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_1421])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2590,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_1421])).

cnf(c_2607,plain,
    ( ~ r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2590])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1895,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3048,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_1741,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1976,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_2363,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_3535,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_4219,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_31,c_29,c_28,c_26,c_2607,c_3048,c_3535])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1431,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4246,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_1431])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1430,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1436,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2824,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1430,c_1436])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_534,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_535,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_611,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_535])).

cnf(c_1420,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_2198,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1420])).

cnf(c_2339,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2198,c_32,c_33,c_34,c_35,c_36,c_37])).

cnf(c_2839,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2824,c_2339])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_439,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_440,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_450,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_440,c_11])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_450,c_24])).

cnf(c_466,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_806,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_466])).

cnf(c_1423,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_3502,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2839,c_1423])).

cnf(c_3503,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3502])).

cnf(c_805,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_466])).

cnf(c_1424,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_3501,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2839,c_1424])).

cnf(c_3583,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_3501])).

cnf(c_4368,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4246,c_32,c_33,c_34,c_35,c_36,c_37,c_3503,c_3583])).

cnf(c_4369,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4368])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1437,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4374,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4369,c_1437])).

cnf(c_1427,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4386,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4374,c_1427])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4394,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4386,c_5])).

cnf(c_2665,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2666,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2665])).

cnf(c_2668,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2666])).

cnf(c_815,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2436,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_2437,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_2439,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2138,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2139,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2138])).

cnf(c_2141,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2108,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2111,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2108])).

cnf(c_809,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1890,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1891,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_1668,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_1669,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1671,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4394,c_3583,c_3503,c_2668,c_2439,c_2141,c_2111,c_1891,c_1671,c_89,c_88,c_9,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:56:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.99  
% 3.09/0.99  ------  iProver source info
% 3.09/0.99  
% 3.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.99  git: non_committed_changes: false
% 3.09/0.99  git: last_make_outside_of_git: false
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options
% 3.09/0.99  
% 3.09/0.99  --out_options                           all
% 3.09/0.99  --tptp_safe_out                         true
% 3.09/0.99  --problem_path                          ""
% 3.09/0.99  --include_path                          ""
% 3.09/0.99  --clausifier                            res/vclausify_rel
% 3.09/0.99  --clausifier_options                    --mode clausify
% 3.09/0.99  --stdin                                 false
% 3.09/0.99  --stats_out                             all
% 3.09/0.99  
% 3.09/0.99  ------ General Options
% 3.09/0.99  
% 3.09/0.99  --fof                                   false
% 3.09/0.99  --time_out_real                         305.
% 3.09/0.99  --time_out_virtual                      -1.
% 3.09/0.99  --symbol_type_check                     false
% 3.09/0.99  --clausify_out                          false
% 3.09/0.99  --sig_cnt_out                           false
% 3.09/0.99  --trig_cnt_out                          false
% 3.09/0.99  --trig_cnt_out_tolerance                1.
% 3.09/0.99  --trig_cnt_out_sk_spl                   false
% 3.09/0.99  --abstr_cl_out                          false
% 3.09/0.99  
% 3.09/0.99  ------ Global Options
% 3.09/0.99  
% 3.09/0.99  --schedule                              default
% 3.09/0.99  --add_important_lit                     false
% 3.09/0.99  --prop_solver_per_cl                    1000
% 3.09/0.99  --min_unsat_core                        false
% 3.09/0.99  --soft_assumptions                      false
% 3.09/0.99  --soft_lemma_size                       3
% 3.09/0.99  --prop_impl_unit_size                   0
% 3.09/0.99  --prop_impl_unit                        []
% 3.09/0.99  --share_sel_clauses                     true
% 3.09/0.99  --reset_solvers                         false
% 3.09/0.99  --bc_imp_inh                            [conj_cone]
% 3.09/0.99  --conj_cone_tolerance                   3.
% 3.09/0.99  --extra_neg_conj                        none
% 3.09/0.99  --large_theory_mode                     true
% 3.09/0.99  --prolific_symb_bound                   200
% 3.09/0.99  --lt_threshold                          2000
% 3.09/0.99  --clause_weak_htbl                      true
% 3.09/0.99  --gc_record_bc_elim                     false
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing Options
% 3.09/0.99  
% 3.09/0.99  --preprocessing_flag                    true
% 3.09/0.99  --time_out_prep_mult                    0.1
% 3.09/0.99  --splitting_mode                        input
% 3.09/0.99  --splitting_grd                         true
% 3.09/0.99  --splitting_cvd                         false
% 3.09/0.99  --splitting_cvd_svl                     false
% 3.09/0.99  --splitting_nvd                         32
% 3.09/0.99  --sub_typing                            true
% 3.09/0.99  --prep_gs_sim                           true
% 3.09/0.99  --prep_unflatten                        true
% 3.09/0.99  --prep_res_sim                          true
% 3.09/0.99  --prep_upred                            true
% 3.09/0.99  --prep_sem_filter                       exhaustive
% 3.09/0.99  --prep_sem_filter_out                   false
% 3.09/0.99  --pred_elim                             true
% 3.09/0.99  --res_sim_input                         true
% 3.09/0.99  --eq_ax_congr_red                       true
% 3.09/0.99  --pure_diseq_elim                       true
% 3.09/0.99  --brand_transform                       false
% 3.09/0.99  --non_eq_to_eq                          false
% 3.09/0.99  --prep_def_merge                        true
% 3.09/0.99  --prep_def_merge_prop_impl              false
% 3.09/0.99  --prep_def_merge_mbd                    true
% 3.09/0.99  --prep_def_merge_tr_red                 false
% 3.09/0.99  --prep_def_merge_tr_cl                  false
% 3.09/0.99  --smt_preprocessing                     true
% 3.09/0.99  --smt_ac_axioms                         fast
% 3.09/0.99  --preprocessed_out                      false
% 3.09/0.99  --preprocessed_stats                    false
% 3.09/0.99  
% 3.09/0.99  ------ Abstraction refinement Options
% 3.09/0.99  
% 3.09/0.99  --abstr_ref                             []
% 3.09/0.99  --abstr_ref_prep                        false
% 3.09/0.99  --abstr_ref_until_sat                   false
% 3.09/0.99  --abstr_ref_sig_restrict                funpre
% 3.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.99  --abstr_ref_under                       []
% 3.09/0.99  
% 3.09/0.99  ------ SAT Options
% 3.09/0.99  
% 3.09/0.99  --sat_mode                              false
% 3.09/0.99  --sat_fm_restart_options                ""
% 3.09/0.99  --sat_gr_def                            false
% 3.09/0.99  --sat_epr_types                         true
% 3.09/0.99  --sat_non_cyclic_types                  false
% 3.09/0.99  --sat_finite_models                     false
% 3.09/0.99  --sat_fm_lemmas                         false
% 3.09/0.99  --sat_fm_prep                           false
% 3.09/0.99  --sat_fm_uc_incr                        true
% 3.09/0.99  --sat_out_model                         small
% 3.09/0.99  --sat_out_clauses                       false
% 3.09/0.99  
% 3.09/0.99  ------ QBF Options
% 3.09/0.99  
% 3.09/0.99  --qbf_mode                              false
% 3.09/0.99  --qbf_elim_univ                         false
% 3.09/0.99  --qbf_dom_inst                          none
% 3.09/0.99  --qbf_dom_pre_inst                      false
% 3.09/0.99  --qbf_sk_in                             false
% 3.09/0.99  --qbf_pred_elim                         true
% 3.09/0.99  --qbf_split                             512
% 3.09/0.99  
% 3.09/0.99  ------ BMC1 Options
% 3.09/0.99  
% 3.09/0.99  --bmc1_incremental                      false
% 3.09/0.99  --bmc1_axioms                           reachable_all
% 3.09/0.99  --bmc1_min_bound                        0
% 3.09/0.99  --bmc1_max_bound                        -1
% 3.09/0.99  --bmc1_max_bound_default                -1
% 3.09/0.99  --bmc1_symbol_reachability              true
% 3.09/0.99  --bmc1_property_lemmas                  false
% 3.09/0.99  --bmc1_k_induction                      false
% 3.09/0.99  --bmc1_non_equiv_states                 false
% 3.09/0.99  --bmc1_deadlock                         false
% 3.09/0.99  --bmc1_ucm                              false
% 3.09/0.99  --bmc1_add_unsat_core                   none
% 3.09/0.99  --bmc1_unsat_core_children              false
% 3.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.99  --bmc1_out_stat                         full
% 3.09/0.99  --bmc1_ground_init                      false
% 3.09/0.99  --bmc1_pre_inst_next_state              false
% 3.09/0.99  --bmc1_pre_inst_state                   false
% 3.09/0.99  --bmc1_pre_inst_reach_state             false
% 3.09/0.99  --bmc1_out_unsat_core                   false
% 3.09/0.99  --bmc1_aig_witness_out                  false
% 3.09/0.99  --bmc1_verbose                          false
% 3.09/0.99  --bmc1_dump_clauses_tptp                false
% 3.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.99  --bmc1_dump_file                        -
% 3.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.99  --bmc1_ucm_extend_mode                  1
% 3.09/0.99  --bmc1_ucm_init_mode                    2
% 3.09/0.99  --bmc1_ucm_cone_mode                    none
% 3.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.99  --bmc1_ucm_relax_model                  4
% 3.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.99  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     num_symb
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.00  --inst_passive_queues_freq              [25;2]
% 3.09/1.00  --inst_dismatching                      true
% 3.09/1.00  --inst_eager_unprocessed_to_passive     true
% 3.09/1.00  --inst_prop_sim_given                   true
% 3.09/1.00  --inst_prop_sim_new                     false
% 3.09/1.00  --inst_subs_new                         false
% 3.09/1.00  --inst_eq_res_simp                      false
% 3.09/1.00  --inst_subs_given                       false
% 3.09/1.00  --inst_orphan_elimination               true
% 3.09/1.00  --inst_learning_loop_flag               true
% 3.09/1.00  --inst_learning_start                   3000
% 3.09/1.00  --inst_learning_factor                  2
% 3.09/1.00  --inst_start_prop_sim_after_learn       3
% 3.09/1.00  --inst_sel_renew                        solver
% 3.09/1.00  --inst_lit_activity_flag                true
% 3.09/1.00  --inst_restr_to_given                   false
% 3.09/1.00  --inst_activity_threshold               500
% 3.09/1.00  --inst_out_proof                        true
% 3.09/1.00  
% 3.09/1.00  ------ Resolution Options
% 3.09/1.00  
% 3.09/1.00  --resolution_flag                       true
% 3.09/1.00  --res_lit_sel                           adaptive
% 3.09/1.00  --res_lit_sel_side                      none
% 3.09/1.00  --res_ordering                          kbo
% 3.09/1.00  --res_to_prop_solver                    active
% 3.09/1.00  --res_prop_simpl_new                    false
% 3.09/1.00  --res_prop_simpl_given                  true
% 3.09/1.00  --res_passive_queue_type                priority_queues
% 3.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.00  --res_passive_queues_freq               [15;5]
% 3.09/1.00  --res_forward_subs                      full
% 3.09/1.00  --res_backward_subs                     full
% 3.09/1.00  --res_forward_subs_resolution           true
% 3.09/1.00  --res_backward_subs_resolution          true
% 3.09/1.00  --res_orphan_elimination                true
% 3.09/1.00  --res_time_limit                        2.
% 3.09/1.00  --res_out_proof                         true
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Options
% 3.09/1.00  
% 3.09/1.00  --superposition_flag                    true
% 3.09/1.00  --sup_passive_queue_type                priority_queues
% 3.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.00  --demod_completeness_check              fast
% 3.09/1.00  --demod_use_ground                      true
% 3.09/1.00  --sup_to_prop_solver                    passive
% 3.09/1.00  --sup_prop_simpl_new                    true
% 3.09/1.00  --sup_prop_simpl_given                  true
% 3.09/1.00  --sup_fun_splitting                     false
% 3.09/1.00  --sup_smt_interval                      50000
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Simplification Setup
% 3.09/1.00  
% 3.09/1.00  --sup_indices_passive                   []
% 3.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_full_bw                           [BwDemod]
% 3.09/1.00  --sup_immed_triv                        [TrivRules]
% 3.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_immed_bw_main                     []
% 3.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  
% 3.09/1.00  ------ Combination Options
% 3.09/1.00  
% 3.09/1.00  --comb_res_mult                         3
% 3.09/1.00  --comb_sup_mult                         2
% 3.09/1.00  --comb_inst_mult                        10
% 3.09/1.00  
% 3.09/1.00  ------ Debug Options
% 3.09/1.00  
% 3.09/1.00  --dbg_backtrace                         false
% 3.09/1.00  --dbg_dump_prop_clauses                 false
% 3.09/1.00  --dbg_dump_prop_clauses_file            -
% 3.09/1.00  --dbg_out_stat                          false
% 3.09/1.00  ------ Parsing...
% 3.09/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/1.00  ------ Proving...
% 3.09/1.00  ------ Problem Properties 
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  clauses                                 27
% 3.09/1.00  conjectures                             6
% 3.09/1.00  EPR                                     7
% 3.09/1.00  Horn                                    25
% 3.09/1.00  unary                                   13
% 3.09/1.00  binary                                  5
% 3.09/1.00  lits                                    75
% 3.09/1.00  lits eq                                 15
% 3.09/1.00  fd_pure                                 0
% 3.09/1.00  fd_pseudo                               0
% 3.09/1.00  fd_cond                                 2
% 3.09/1.00  fd_pseudo_cond                          1
% 3.09/1.00  AC symbols                              0
% 3.09/1.00  
% 3.09/1.00  ------ Schedule dynamic 5 is on 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  Current options:
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     none
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.00  --inst_passive_queues_freq              [25;2]
% 3.09/1.00  --inst_dismatching                      true
% 3.09/1.00  --inst_eager_unprocessed_to_passive     true
% 3.09/1.00  --inst_prop_sim_given                   true
% 3.09/1.00  --inst_prop_sim_new                     false
% 3.09/1.00  --inst_subs_new                         false
% 3.09/1.00  --inst_eq_res_simp                      false
% 3.09/1.00  --inst_subs_given                       false
% 3.09/1.00  --inst_orphan_elimination               true
% 3.09/1.00  --inst_learning_loop_flag               true
% 3.09/1.00  --inst_learning_start                   3000
% 3.09/1.00  --inst_learning_factor                  2
% 3.09/1.00  --inst_start_prop_sim_after_learn       3
% 3.09/1.00  --inst_sel_renew                        solver
% 3.09/1.00  --inst_lit_activity_flag                true
% 3.09/1.00  --inst_restr_to_given                   false
% 3.09/1.00  --inst_activity_threshold               500
% 3.09/1.00  --inst_out_proof                        true
% 3.09/1.00  
% 3.09/1.00  ------ Resolution Options
% 3.09/1.00  
% 3.09/1.00  --resolution_flag                       false
% 3.09/1.00  --res_lit_sel                           adaptive
% 3.09/1.00  --res_lit_sel_side                      none
% 3.09/1.00  --res_ordering                          kbo
% 3.09/1.00  --res_to_prop_solver                    active
% 3.09/1.00  --res_prop_simpl_new                    false
% 3.09/1.00  --res_prop_simpl_given                  true
% 3.09/1.00  --res_passive_queue_type                priority_queues
% 3.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.00  --res_passive_queues_freq               [15;5]
% 3.09/1.00  --res_forward_subs                      full
% 3.09/1.00  --res_backward_subs                     full
% 3.09/1.00  --res_forward_subs_resolution           true
% 3.09/1.00  --res_backward_subs_resolution          true
% 3.09/1.00  --res_orphan_elimination                true
% 3.09/1.00  --res_time_limit                        2.
% 3.09/1.00  --res_out_proof                         true
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Options
% 3.09/1.00  
% 3.09/1.00  --superposition_flag                    true
% 3.09/1.00  --sup_passive_queue_type                priority_queues
% 3.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.00  --demod_completeness_check              fast
% 3.09/1.00  --demod_use_ground                      true
% 3.09/1.00  --sup_to_prop_solver                    passive
% 3.09/1.00  --sup_prop_simpl_new                    true
% 3.09/1.00  --sup_prop_simpl_given                  true
% 3.09/1.00  --sup_fun_splitting                     false
% 3.09/1.00  --sup_smt_interval                      50000
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Simplification Setup
% 3.09/1.00  
% 3.09/1.00  --sup_indices_passive                   []
% 3.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_full_bw                           [BwDemod]
% 3.09/1.00  --sup_immed_triv                        [TrivRules]
% 3.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_immed_bw_main                     []
% 3.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  
% 3.09/1.00  ------ Combination Options
% 3.09/1.00  
% 3.09/1.00  --comb_res_mult                         3
% 3.09/1.00  --comb_sup_mult                         2
% 3.09/1.00  --comb_inst_mult                        10
% 3.09/1.00  
% 3.09/1.00  ------ Debug Options
% 3.09/1.00  
% 3.09/1.00  --dbg_backtrace                         false
% 3.09/1.00  --dbg_dump_prop_clauses                 false
% 3.09/1.00  --dbg_dump_prop_clauses_file            -
% 3.09/1.00  --dbg_out_stat                          false
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  ------ Proving...
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  % SZS status Theorem for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  fof(f12,axiom,(
% 3.09/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f28,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.09/1.00    inference(ennf_transformation,[],[f12])).
% 3.09/1.00  
% 3.09/1.00  fof(f29,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.09/1.00    inference(flattening,[],[f28])).
% 3.09/1.00  
% 3.09/1.00  fof(f65,plain,(
% 3.09/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f29])).
% 3.09/1.00  
% 3.09/1.00  fof(f10,axiom,(
% 3.09/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f24,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.09/1.00    inference(ennf_transformation,[],[f10])).
% 3.09/1.00  
% 3.09/1.00  fof(f25,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(flattening,[],[f24])).
% 3.09/1.00  
% 3.09/1.00  fof(f41,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(nnf_transformation,[],[f25])).
% 3.09/1.00  
% 3.09/1.00  fof(f60,plain,(
% 3.09/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f41])).
% 3.09/1.00  
% 3.09/1.00  fof(f17,conjecture,(
% 3.09/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f18,negated_conjecture,(
% 3.09/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.09/1.00    inference(negated_conjecture,[],[f17])).
% 3.09/1.00  
% 3.09/1.00  fof(f34,plain,(
% 3.09/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.09/1.00    inference(ennf_transformation,[],[f18])).
% 3.09/1.00  
% 3.09/1.00  fof(f35,plain,(
% 3.09/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.09/1.00    inference(flattening,[],[f34])).
% 3.09/1.00  
% 3.09/1.00  fof(f44,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.09/1.00    introduced(choice_axiom,[])).
% 3.09/1.00  
% 3.09/1.00  fof(f43,plain,(
% 3.09/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.09/1.00    introduced(choice_axiom,[])).
% 3.09/1.00  
% 3.09/1.00  fof(f45,plain,(
% 3.09/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.09/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f44,f43])).
% 3.09/1.00  
% 3.09/1.00  fof(f77,plain,(
% 3.09/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f13,axiom,(
% 3.09/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f19,plain,(
% 3.09/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.09/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.09/1.00  
% 3.09/1.00  fof(f66,plain,(
% 3.09/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f19])).
% 3.09/1.00  
% 3.09/1.00  fof(f71,plain,(
% 3.09/1.00    v1_funct_1(sK2)),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f73,plain,(
% 3.09/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f74,plain,(
% 3.09/1.00    v1_funct_1(sK3)),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f76,plain,(
% 3.09/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f4,axiom,(
% 3.09/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f40,plain,(
% 3.09/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.09/1.00    inference(nnf_transformation,[],[f4])).
% 3.09/1.00  
% 3.09/1.00  fof(f54,plain,(
% 3.09/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f40])).
% 3.09/1.00  
% 3.09/1.00  fof(f53,plain,(
% 3.09/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f40])).
% 3.09/1.00  
% 3.09/1.00  fof(f16,axiom,(
% 3.09/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f32,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.09/1.00    inference(ennf_transformation,[],[f16])).
% 3.09/1.00  
% 3.09/1.00  fof(f33,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.09/1.00    inference(flattening,[],[f32])).
% 3.09/1.00  
% 3.09/1.00  fof(f69,plain,(
% 3.09/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f33])).
% 3.09/1.00  
% 3.09/1.00  fof(f72,plain,(
% 3.09/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f75,plain,(
% 3.09/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f9,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f23,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f9])).
% 3.09/1.00  
% 3.09/1.00  fof(f59,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f23])).
% 3.09/1.00  
% 3.09/1.00  fof(f15,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f30,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.09/1.00    inference(ennf_transformation,[],[f15])).
% 3.09/1.00  
% 3.09/1.00  fof(f31,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.09/1.00    inference(flattening,[],[f30])).
% 3.09/1.00  
% 3.09/1.00  fof(f68,plain,(
% 3.09/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f31])).
% 3.09/1.00  
% 3.09/1.00  fof(f8,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f20,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.09/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.09/1.00  
% 3.09/1.00  fof(f22,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f20])).
% 3.09/1.00  
% 3.09/1.00  fof(f58,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f22])).
% 3.09/1.00  
% 3.09/1.00  fof(f11,axiom,(
% 3.09/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f26,plain,(
% 3.09/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.09/1.00    inference(ennf_transformation,[],[f11])).
% 3.09/1.00  
% 3.09/1.00  fof(f27,plain,(
% 3.09/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(flattening,[],[f26])).
% 3.09/1.00  
% 3.09/1.00  fof(f42,plain,(
% 3.09/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(nnf_transformation,[],[f27])).
% 3.09/1.00  
% 3.09/1.00  fof(f63,plain,(
% 3.09/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f42])).
% 3.09/1.00  
% 3.09/1.00  fof(f86,plain,(
% 3.09/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(equality_resolution,[],[f63])).
% 3.09/1.00  
% 3.09/1.00  fof(f7,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f21,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f7])).
% 3.09/1.00  
% 3.09/1.00  fof(f57,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f21])).
% 3.09/1.00  
% 3.09/1.00  fof(f78,plain,(
% 3.09/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.09/1.00    inference(cnf_transformation,[],[f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f6,axiom,(
% 3.09/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f56,plain,(
% 3.09/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f6])).
% 3.09/1.00  
% 3.09/1.00  fof(f14,axiom,(
% 3.09/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f67,plain,(
% 3.09/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f14])).
% 3.09/1.00  
% 3.09/1.00  fof(f80,plain,(
% 3.09/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.09/1.00    inference(definition_unfolding,[],[f56,f67])).
% 3.09/1.00  
% 3.09/1.00  fof(f3,axiom,(
% 3.09/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f38,plain,(
% 3.09/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/1.00    inference(nnf_transformation,[],[f3])).
% 3.09/1.00  
% 3.09/1.00  fof(f39,plain,(
% 3.09/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/1.00    inference(flattening,[],[f38])).
% 3.09/1.00  
% 3.09/1.00  fof(f51,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.09/1.00    inference(cnf_transformation,[],[f39])).
% 3.09/1.00  
% 3.09/1.00  fof(f84,plain,(
% 3.09/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.09/1.00    inference(equality_resolution,[],[f51])).
% 3.09/1.00  
% 3.09/1.00  fof(f1,axiom,(
% 3.09/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f36,plain,(
% 3.09/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.00    inference(nnf_transformation,[],[f1])).
% 3.09/1.00  
% 3.09/1.00  fof(f37,plain,(
% 3.09/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.00    inference(flattening,[],[f36])).
% 3.09/1.00  
% 3.09/1.00  fof(f48,plain,(
% 3.09/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f37])).
% 3.09/1.00  
% 3.09/1.00  fof(f2,axiom,(
% 3.09/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f49,plain,(
% 3.09/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f2])).
% 3.09/1.00  
% 3.09/1.00  fof(f50,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f39])).
% 3.09/1.00  
% 3.09/1.00  fof(f5,axiom,(
% 3.09/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f55,plain,(
% 3.09/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.09/1.00    inference(cnf_transformation,[],[f5])).
% 3.09/1.00  
% 3.09/1.00  fof(f79,plain,(
% 3.09/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.09/1.00    inference(definition_unfolding,[],[f55,f67])).
% 3.09/1.00  
% 3.09/1.00  cnf(c_18,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.09/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(X3) ),
% 3.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1435,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.09/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.09/1.00      | v1_funct_1(X0) != iProver_top
% 3.09/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_15,plain,
% 3.09/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | X3 = X2 ),
% 3.09/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_25,negated_conjecture,
% 3.09/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_521,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | X3 = X0
% 3.09/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.09/1.00      | k6_partfun1(sK0) != X3
% 3.09/1.00      | sK0 != X2
% 3.09/1.00      | sK0 != X1 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_522,plain,
% 3.09/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_521]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_20,plain,
% 3.09/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_530,plain,
% 3.09/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.09/1.00      inference(forward_subsumption_resolution,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_522,c_20]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1421,plain,
% 3.09/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3757,plain,
% 3.09/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.09/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.00      | v1_funct_1(sK2) != iProver_top
% 3.09/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1435,c_1421]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_31,negated_conjecture,
% 3.09/1.00      ( v1_funct_1(sK2) ),
% 3.09/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_29,negated_conjecture,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_28,negated_conjecture,
% 3.09/1.00      ( v1_funct_1(sK3) ),
% 3.09/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_26,negated_conjecture,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_7,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1439,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.09/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2590,plain,
% 3.09/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.09/1.00      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1439,c_1421]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2607,plain,
% 3.09/1.00      ( ~ r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0))
% 3.09/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2590]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_8,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1895,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3048,plain,
% 3.09/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.00      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1895]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1741,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.09/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1976,plain,
% 3.09/1.00      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
% 3.09/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.09/1.00      | ~ v1_funct_1(sK2)
% 3.09/1.00      | ~ v1_funct_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1741]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2363,plain,
% 3.09/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.09/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | ~ v1_funct_1(sK2)
% 3.09/1.00      | ~ v1_funct_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3535,plain,
% 3.09/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.09/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.09/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.09/1.00      | ~ v1_funct_1(sK2)
% 3.09/1.00      | ~ v1_funct_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4219,plain,
% 3.09/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_3757,c_31,c_29,c_28,c_26,c_2607,c_3048,c_3535]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_23,plain,
% 3.09/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.09/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(X3)
% 3.09/1.00      | v2_funct_1(X3)
% 3.09/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.09/1.00      | k1_xboole_0 = X2 ),
% 3.09/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1431,plain,
% 3.09/1.00      ( k1_xboole_0 = X0
% 3.09/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.09/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.09/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.09/1.00      | v1_funct_1(X1) != iProver_top
% 3.09/1.00      | v1_funct_1(X3) != iProver_top
% 3.09/1.00      | v2_funct_1(X3) = iProver_top
% 3.09/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4246,plain,
% 3.09/1.00      ( sK0 = k1_xboole_0
% 3.09/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.09/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.09/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.00      | v1_funct_1(sK2) != iProver_top
% 3.09/1.00      | v1_funct_1(sK3) != iProver_top
% 3.09/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.09/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_4219,c_1431]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_32,plain,
% 3.09/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_30,negated_conjecture,
% 3.09/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_33,plain,
% 3.09/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_34,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_35,plain,
% 3.09/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_27,negated_conjecture,
% 3.09/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_36,plain,
% 3.09/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_37,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1430,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_13,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1436,plain,
% 3.09/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.09/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2824,plain,
% 3.09/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1430,c_1436]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_21,plain,
% 3.09/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.09/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.09/1.00      | ~ v1_funct_2(X3,X1,X0)
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | ~ v1_funct_1(X2)
% 3.09/1.00      | ~ v1_funct_1(X3)
% 3.09/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_534,plain,
% 3.09/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.09/1.00      | ~ v1_funct_2(X3,X2,X1)
% 3.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(X3)
% 3.09/1.00      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.00      | k2_relset_1(X1,X2,X0) = X2
% 3.09/1.00      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.09/1.00      | sK0 != X2 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_535,plain,
% 3.09/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.09/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(X2)
% 3.09/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 3.09/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_611,plain,
% 3.09/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 3.09/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_funct_1(X2)
% 3.09/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.09/1.00      inference(equality_resolution_simp,[status(thm)],[c_535]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1420,plain,
% 3.09/1.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.09/1.00      | k2_relset_1(X0,sK0,X2) = sK0
% 3.09/1.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.09/1.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.09/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.09/1.00      | v1_funct_1(X2) != iProver_top
% 3.09/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2198,plain,
% 3.09/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.09/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.09/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.09/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.09/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.09/1.00      | v1_funct_1(sK2) != iProver_top
% 3.09/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.09/1.00      inference(equality_resolution,[status(thm)],[c_1420]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2339,plain,
% 3.09/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_2198,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2839,plain,
% 3.09/1.00      ( k2_relat_1(sK3) = sK0 ),
% 3.09/1.00      inference(light_normalisation,[status(thm)],[c_2824,c_2339]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_12,plain,
% 3.09/1.00      ( v5_relat_1(X0,X1)
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_16,plain,
% 3.09/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.09/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_439,plain,
% 3.09/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | X0 != X1
% 3.09/1.00      | k2_relat_1(X0) != X3 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_440,plain,
% 3.09/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_439]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_11,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_450,plain,
% 3.09/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.09/1.00      inference(forward_subsumption_resolution,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_440,c_11]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_24,negated_conjecture,
% 3.09/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.09/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_465,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.09/1.00      | ~ v2_funct_1(sK2)
% 3.09/1.00      | k2_relat_1(X0) != sK0
% 3.09/1.00      | sK3 != X0 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_450,c_24]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_466,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.09/1.00      | ~ v2_funct_1(sK2)
% 3.09/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_806,plain,
% 3.09/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.09/1.00      inference(splitting,
% 3.09/1.00                [splitting(split),new_symbols(definition,[])],
% 3.09/1.00                [c_466]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1423,plain,
% 3.09/1.00      ( k2_relat_1(sK3) != sK0
% 3.09/1.00      | v2_funct_1(sK2) != iProver_top
% 3.09/1.00      | sP0_iProver_split = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3502,plain,
% 3.09/1.00      ( sK0 != sK0
% 3.09/1.00      | v2_funct_1(sK2) != iProver_top
% 3.09/1.00      | sP0_iProver_split = iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_2839,c_1423]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3503,plain,
% 3.09/1.00      ( v2_funct_1(sK2) != iProver_top
% 3.09/1.00      | sP0_iProver_split = iProver_top ),
% 3.09/1.00      inference(equality_resolution_simp,[status(thm)],[c_3502]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_805,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.09/1.00      | ~ sP0_iProver_split ),
% 3.09/1.00      inference(splitting,
% 3.09/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.09/1.00                [c_466]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1424,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.09/1.00      | sP0_iProver_split != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3501,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.09/1.00      | sP0_iProver_split != iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_2839,c_1424]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3583,plain,
% 3.09/1.00      ( sP0_iProver_split != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1430,c_3501]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4368,plain,
% 3.09/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_4246,c_32,c_33,c_34,c_35,c_36,c_37,c_3503,c_3583]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4369,plain,
% 3.09/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.09/1.00      inference(renaming,[status(thm)],[c_4368]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_10,plain,
% 3.09/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1437,plain,
% 3.09/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4374,plain,
% 3.09/1.00      ( sK0 = k1_xboole_0 ),
% 3.09/1.00      inference(forward_subsumption_resolution,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_4369,c_1437]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1427,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4386,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_4374,c_1427]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5,plain,
% 3.09/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4394,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_4386,c_5]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2665,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2666,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.09/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2665]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2668,plain,
% 3.09/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/1.00      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_2666]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_815,plain,
% 3.09/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.09/1.00      theory(equality) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2436,plain,
% 3.09/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_815]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2437,plain,
% 3.09/1.00      ( sK2 != X0
% 3.09/1.00      | v2_funct_1(X0) != iProver_top
% 3.09/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2439,plain,
% 3.09/1.00      ( sK2 != k1_xboole_0
% 3.09/1.00      | v2_funct_1(sK2) = iProver_top
% 3.09/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_2437]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_0,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.09/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2138,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2139,plain,
% 3.09/1.00      ( sK2 = X0
% 3.09/1.00      | r1_tarski(X0,sK2) != iProver_top
% 3.09/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2138]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2141,plain,
% 3.09/1.00      ( sK2 = k1_xboole_0
% 3.09/1.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.09/1.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2108,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2111,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2108]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_809,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1890,plain,
% 3.09/1.00      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_809]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1891,plain,
% 3.09/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.09/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.09/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1890]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1668,plain,
% 3.09/1.00      ( v2_funct_1(X0)
% 3.09/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 3.09/1.00      | X0 != k6_partfun1(X1) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_815]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1669,plain,
% 3.09/1.00      ( X0 != k6_partfun1(X1)
% 3.09/1.00      | v2_funct_1(X0) = iProver_top
% 3.09/1.00      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1671,plain,
% 3.09/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.09/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.09/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1669]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_89,plain,
% 3.09/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_6,plain,
% 3.09/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.09/1.00      | k1_xboole_0 = X1
% 3.09/1.00      | k1_xboole_0 = X0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_88,plain,
% 3.09/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.09/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_9,plain,
% 3.09/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_79,plain,
% 3.09/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_81,plain,
% 3.09/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_79]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(contradiction,plain,
% 3.09/1.00      ( $false ),
% 3.09/1.00      inference(minisat,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_4394,c_3583,c_3503,c_2668,c_2439,c_2141,c_2111,c_1891,
% 3.09/1.00                 c_1671,c_89,c_88,c_9,c_81]) ).
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  ------                               Statistics
% 3.09/1.00  
% 3.09/1.00  ------ General
% 3.09/1.00  
% 3.09/1.00  abstr_ref_over_cycles:                  0
% 3.09/1.00  abstr_ref_under_cycles:                 0
% 3.09/1.00  gc_basic_clause_elim:                   0
% 3.09/1.00  forced_gc_time:                         0
% 3.09/1.00  parsing_time:                           0.01
% 3.09/1.00  unif_index_cands_time:                  0.
% 3.09/1.00  unif_index_add_time:                    0.
% 3.09/1.00  orderings_time:                         0.
% 3.09/1.00  out_proof_time:                         0.013
% 3.09/1.00  total_time:                             0.17
% 3.09/1.00  num_of_symbols:                         52
% 3.09/1.00  num_of_terms:                           5710
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing
% 3.09/1.00  
% 3.09/1.00  num_of_splits:                          1
% 3.09/1.00  num_of_split_atoms:                     1
% 3.09/1.00  num_of_reused_defs:                     0
% 3.09/1.00  num_eq_ax_congr_red:                    13
% 3.09/1.00  num_of_sem_filtered_clauses:            1
% 3.09/1.00  num_of_subtypes:                        0
% 3.09/1.00  monotx_restored_types:                  0
% 3.09/1.00  sat_num_of_epr_types:                   0
% 3.09/1.00  sat_num_of_non_cyclic_types:            0
% 3.09/1.00  sat_guarded_non_collapsed_types:        0
% 3.09/1.00  num_pure_diseq_elim:                    0
% 3.09/1.00  simp_replaced_by:                       0
% 3.09/1.00  res_preprocessed:                       138
% 3.09/1.00  prep_upred:                             0
% 3.09/1.00  prep_unflattend:                        17
% 3.09/1.00  smt_new_axioms:                         0
% 3.09/1.00  pred_elim_cands:                        5
% 3.09/1.00  pred_elim:                              4
% 3.09/1.00  pred_elim_cl:                           5
% 3.09/1.00  pred_elim_cycles:                       7
% 3.09/1.00  merged_defs:                            8
% 3.09/1.00  merged_defs_ncl:                        0
% 3.09/1.00  bin_hyper_res:                          8
% 3.09/1.00  prep_cycles:                            4
% 3.09/1.00  pred_elim_time:                         0.006
% 3.09/1.00  splitting_time:                         0.
% 3.09/1.00  sem_filter_time:                        0.
% 3.09/1.00  monotx_time:                            0.001
% 3.09/1.00  subtype_inf_time:                       0.
% 3.09/1.00  
% 3.09/1.00  ------ Problem properties
% 3.09/1.00  
% 3.09/1.00  clauses:                                27
% 3.09/1.00  conjectures:                            6
% 3.09/1.00  epr:                                    7
% 3.09/1.00  horn:                                   25
% 3.09/1.00  ground:                                 9
% 3.09/1.00  unary:                                  13
% 3.09/1.00  binary:                                 5
% 3.09/1.00  lits:                                   75
% 3.09/1.00  lits_eq:                                15
% 3.09/1.00  fd_pure:                                0
% 3.09/1.00  fd_pseudo:                              0
% 3.09/1.00  fd_cond:                                2
% 3.09/1.00  fd_pseudo_cond:                         1
% 3.09/1.00  ac_symbols:                             0
% 3.09/1.00  
% 3.09/1.00  ------ Propositional Solver
% 3.09/1.00  
% 3.09/1.00  prop_solver_calls:                      27
% 3.09/1.00  prop_fast_solver_calls:                 966
% 3.09/1.00  smt_solver_calls:                       0
% 3.09/1.00  smt_fast_solver_calls:                  0
% 3.09/1.00  prop_num_of_clauses:                    1568
% 3.09/1.00  prop_preprocess_simplified:             5116
% 3.09/1.00  prop_fo_subsumed:                       23
% 3.09/1.00  prop_solver_time:                       0.
% 3.09/1.00  smt_solver_time:                        0.
% 3.09/1.00  smt_fast_solver_time:                   0.
% 3.09/1.00  prop_fast_solver_time:                  0.
% 3.09/1.00  prop_unsat_core_time:                   0.
% 3.09/1.00  
% 3.09/1.00  ------ QBF
% 3.09/1.00  
% 3.09/1.00  qbf_q_res:                              0
% 3.09/1.00  qbf_num_tautologies:                    0
% 3.09/1.00  qbf_prep_cycles:                        0
% 3.09/1.00  
% 3.09/1.00  ------ BMC1
% 3.09/1.00  
% 3.09/1.00  bmc1_current_bound:                     -1
% 3.09/1.00  bmc1_last_solved_bound:                 -1
% 3.09/1.00  bmc1_unsat_core_size:                   -1
% 3.09/1.00  bmc1_unsat_core_parents_size:           -1
% 3.09/1.00  bmc1_merge_next_fun:                    0
% 3.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation
% 3.09/1.00  
% 3.09/1.00  inst_num_of_clauses:                    466
% 3.09/1.00  inst_num_in_passive:                    103
% 3.09/1.00  inst_num_in_active:                     258
% 3.09/1.00  inst_num_in_unprocessed:                105
% 3.09/1.00  inst_num_of_loops:                      270
% 3.09/1.00  inst_num_of_learning_restarts:          0
% 3.09/1.00  inst_num_moves_active_passive:          9
% 3.09/1.00  inst_lit_activity:                      0
% 3.09/1.00  inst_lit_activity_moves:                0
% 3.09/1.00  inst_num_tautologies:                   0
% 3.09/1.00  inst_num_prop_implied:                  0
% 3.09/1.00  inst_num_existing_simplified:           0
% 3.09/1.00  inst_num_eq_res_simplified:             0
% 3.09/1.00  inst_num_child_elim:                    0
% 3.09/1.00  inst_num_of_dismatching_blockings:      68
% 3.09/1.00  inst_num_of_non_proper_insts:           456
% 3.09/1.00  inst_num_of_duplicates:                 0
% 3.09/1.00  inst_inst_num_from_inst_to_res:         0
% 3.09/1.00  inst_dismatching_checking_time:         0.
% 3.09/1.00  
% 3.09/1.00  ------ Resolution
% 3.09/1.00  
% 3.09/1.00  res_num_of_clauses:                     0
% 3.09/1.00  res_num_in_passive:                     0
% 3.09/1.00  res_num_in_active:                      0
% 3.09/1.00  res_num_of_loops:                       142
% 3.09/1.00  res_forward_subset_subsumed:            24
% 3.09/1.00  res_backward_subset_subsumed:           0
% 3.09/1.00  res_forward_subsumed:                   0
% 3.09/1.00  res_backward_subsumed:                  0
% 3.09/1.00  res_forward_subsumption_resolution:     4
% 3.09/1.00  res_backward_subsumption_resolution:    0
% 3.09/1.00  res_clause_to_clause_subsumption:       222
% 3.09/1.00  res_orphan_elimination:                 0
% 3.09/1.00  res_tautology_del:                      40
% 3.09/1.00  res_num_eq_res_simplified:              1
% 3.09/1.00  res_num_sel_changes:                    0
% 3.09/1.00  res_moves_from_active_to_pass:          0
% 3.09/1.00  
% 3.09/1.00  ------ Superposition
% 3.09/1.00  
% 3.09/1.00  sup_time_total:                         0.
% 3.09/1.00  sup_time_generating:                    0.
% 3.09/1.00  sup_time_sim_full:                      0.
% 3.09/1.00  sup_time_sim_immed:                     0.
% 3.09/1.00  
% 3.09/1.00  sup_num_of_clauses:                     54
% 3.09/1.00  sup_num_in_active:                      32
% 3.09/1.00  sup_num_in_passive:                     22
% 3.09/1.00  sup_num_of_loops:                       53
% 3.09/1.00  sup_fw_superposition:                   35
% 3.09/1.00  sup_bw_superposition:                   18
% 3.09/1.00  sup_immediate_simplified:               18
% 3.09/1.00  sup_given_eliminated:                   1
% 3.09/1.00  comparisons_done:                       0
% 3.09/1.00  comparisons_avoided:                    0
% 3.09/1.00  
% 3.09/1.00  ------ Simplifications
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  sim_fw_subset_subsumed:                 0
% 3.09/1.00  sim_bw_subset_subsumed:                 1
% 3.09/1.00  sim_fw_subsumed:                        2
% 3.09/1.00  sim_bw_subsumed:                        1
% 3.09/1.00  sim_fw_subsumption_res:                 1
% 3.09/1.00  sim_bw_subsumption_res:                 0
% 3.09/1.00  sim_tautology_del:                      1
% 3.09/1.00  sim_eq_tautology_del:                   3
% 3.09/1.00  sim_eq_res_simp:                        1
% 3.09/1.00  sim_fw_demodulated:                     11
% 3.09/1.00  sim_bw_demodulated:                     19
% 3.09/1.00  sim_light_normalised:                   6
% 3.09/1.00  sim_joinable_taut:                      0
% 3.09/1.00  sim_joinable_simp:                      0
% 3.09/1.00  sim_ac_normalised:                      0
% 3.09/1.00  sim_smt_subsumption:                    0
% 3.09/1.00  
%------------------------------------------------------------------------------
