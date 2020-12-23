%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:45 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 456 expanded)
%              Number of clauses        :   90 ( 134 expanded)
%              Number of leaves         :   24 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  570 (2695 expanded)
%              Number of equality atoms :  150 ( 207 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f73,plain,(
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

fof(f72,plain,
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

fof(f74,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f73,f72])).

fof(f124,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

fof(f127,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f128,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f25,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f122,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f28,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f119,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f130,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f96,f119])).

fof(f19,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f105,f119])).

fof(f29,axiom,(
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

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f123,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f74])).

fof(f126,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f100,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f142,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f112])).

fof(f129,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f139,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

cnf(c_51,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1694,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_48,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1697,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1700,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6071,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1700])).

cnf(c_50,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_57,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_6437,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6071,c_57])).

cnf(c_6438,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6437])).

cnf(c_6446,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_6438])).

cnf(c_35,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_47,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_47])).

cnf(c_568,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_40,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_576,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_568,c_40])).

cnf(c_1690,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1775,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2090,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_53,c_51,c_50,c_48,c_576,c_1775])).

cnf(c_6449,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6446,c_2090])).

cnf(c_54,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_7115,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6449,c_54])).

cnf(c_17,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1711,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7118,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7115,c_1711])).

cnf(c_20,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_7121,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7118,c_20])).

cnf(c_29,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1706,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1698,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4133,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_1698])).

cnf(c_52,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_55,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_49,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_58,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_181,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_22,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_319,plain,
    ( v2_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_22,c_8])).

cnf(c_1784,plain,
    ( v2_funct_1(sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1785,plain,
    ( v2_funct_1(sK2) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1879,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_1880,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1879])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1932,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1933,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_1004,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2015,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_2016,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_2018,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_4543,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4133,c_54,c_55,c_56,c_57,c_58,c_59,c_181,c_1785,c_1880,c_1933,c_2018])).

cnf(c_4547,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1706,c_4543])).

cnf(c_32,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_32,c_12])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_648,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_31])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_1687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2774,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1687])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1722,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4272,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_1722])).

cnf(c_1705,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3425,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1705])).

cnf(c_1844,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2085,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_2086,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2085])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_46,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_585,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_46])).

cnf(c_586,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_697,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_586])).

cnf(c_698,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_708,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_698,c_2])).

cnf(c_712,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7121,c_4547,c_4272,c_3425,c_2086,c_712,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    ""
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         true
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     num_symb
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       true
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     true
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_input_bw                          []
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 43
% 3.77/0.99  conjectures                             6
% 3.77/0.99  EPR                                     11
% 3.77/0.99  Horn                                    42
% 3.77/0.99  unary                                   15
% 3.77/0.99  binary                                  11
% 3.77/0.99  lits                                    105
% 3.77/0.99  lits eq                                 13
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 3
% 3.77/0.99  fd_pseudo_cond                          2
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Schedule dynamic 5 is on 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  ------ Input Options
% 3.77/0.99  
% 3.77/0.99  --out_options                           all
% 3.77/0.99  --tptp_safe_out                         true
% 3.77/0.99  --problem_path                          ""
% 3.77/0.99  --include_path                          ""
% 3.77/0.99  --clausifier                            res/vclausify_rel
% 3.77/0.99  --clausifier_options                    ""
% 3.77/0.99  --stdin                                 false
% 3.77/0.99  --stats_out                             all
% 3.77/0.99  
% 3.77/0.99  ------ General Options
% 3.77/0.99  
% 3.77/0.99  --fof                                   false
% 3.77/0.99  --time_out_real                         305.
% 3.77/0.99  --time_out_virtual                      -1.
% 3.77/0.99  --symbol_type_check                     false
% 3.77/0.99  --clausify_out                          false
% 3.77/0.99  --sig_cnt_out                           false
% 3.77/0.99  --trig_cnt_out                          false
% 3.77/0.99  --trig_cnt_out_tolerance                1.
% 3.77/0.99  --trig_cnt_out_sk_spl                   false
% 3.77/0.99  --abstr_cl_out                          false
% 3.77/0.99  
% 3.77/0.99  ------ Global Options
% 3.77/0.99  
% 3.77/0.99  --schedule                              default
% 3.77/0.99  --add_important_lit                     false
% 3.77/0.99  --prop_solver_per_cl                    1000
% 3.77/0.99  --min_unsat_core                        false
% 3.77/0.99  --soft_assumptions                      false
% 3.77/0.99  --soft_lemma_size                       3
% 3.77/0.99  --prop_impl_unit_size                   0
% 3.77/0.99  --prop_impl_unit                        []
% 3.77/0.99  --share_sel_clauses                     true
% 3.77/0.99  --reset_solvers                         false
% 3.77/0.99  --bc_imp_inh                            [conj_cone]
% 3.77/0.99  --conj_cone_tolerance                   3.
% 3.77/0.99  --extra_neg_conj                        none
% 3.77/0.99  --large_theory_mode                     true
% 3.77/0.99  --prolific_symb_bound                   200
% 3.77/0.99  --lt_threshold                          2000
% 3.77/0.99  --clause_weak_htbl                      true
% 3.77/0.99  --gc_record_bc_elim                     false
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing Options
% 3.77/0.99  
% 3.77/0.99  --preprocessing_flag                    true
% 3.77/0.99  --time_out_prep_mult                    0.1
% 3.77/0.99  --splitting_mode                        input
% 3.77/0.99  --splitting_grd                         true
% 3.77/0.99  --splitting_cvd                         false
% 3.77/0.99  --splitting_cvd_svl                     false
% 3.77/0.99  --splitting_nvd                         32
% 3.77/0.99  --sub_typing                            true
% 3.77/0.99  --prep_gs_sim                           true
% 3.77/0.99  --prep_unflatten                        true
% 3.77/0.99  --prep_res_sim                          true
% 3.77/0.99  --prep_upred                            true
% 3.77/0.99  --prep_sem_filter                       exhaustive
% 3.77/0.99  --prep_sem_filter_out                   false
% 3.77/0.99  --pred_elim                             true
% 3.77/0.99  --res_sim_input                         true
% 3.77/0.99  --eq_ax_congr_red                       true
% 3.77/0.99  --pure_diseq_elim                       true
% 3.77/0.99  --brand_transform                       false
% 3.77/0.99  --non_eq_to_eq                          false
% 3.77/0.99  --prep_def_merge                        true
% 3.77/0.99  --prep_def_merge_prop_impl              false
% 3.77/0.99  --prep_def_merge_mbd                    true
% 3.77/0.99  --prep_def_merge_tr_red                 false
% 3.77/0.99  --prep_def_merge_tr_cl                  false
% 3.77/0.99  --smt_preprocessing                     true
% 3.77/0.99  --smt_ac_axioms                         fast
% 3.77/0.99  --preprocessed_out                      false
% 3.77/0.99  --preprocessed_stats                    false
% 3.77/0.99  
% 3.77/0.99  ------ Abstraction refinement Options
% 3.77/0.99  
% 3.77/0.99  --abstr_ref                             []
% 3.77/0.99  --abstr_ref_prep                        false
% 3.77/0.99  --abstr_ref_until_sat                   false
% 3.77/0.99  --abstr_ref_sig_restrict                funpre
% 3.77/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.77/0.99  --abstr_ref_under                       []
% 3.77/0.99  
% 3.77/0.99  ------ SAT Options
% 3.77/0.99  
% 3.77/0.99  --sat_mode                              false
% 3.77/0.99  --sat_fm_restart_options                ""
% 3.77/0.99  --sat_gr_def                            false
% 3.77/0.99  --sat_epr_types                         true
% 3.77/0.99  --sat_non_cyclic_types                  false
% 3.77/0.99  --sat_finite_models                     false
% 3.77/0.99  --sat_fm_lemmas                         false
% 3.77/0.99  --sat_fm_prep                           false
% 3.77/0.99  --sat_fm_uc_incr                        true
% 3.77/0.99  --sat_out_model                         small
% 3.77/0.99  --sat_out_clauses                       false
% 3.77/0.99  
% 3.77/0.99  ------ QBF Options
% 3.77/0.99  
% 3.77/0.99  --qbf_mode                              false
% 3.77/0.99  --qbf_elim_univ                         false
% 3.77/0.99  --qbf_dom_inst                          none
% 3.77/0.99  --qbf_dom_pre_inst                      false
% 3.77/0.99  --qbf_sk_in                             false
% 3.77/0.99  --qbf_pred_elim                         true
% 3.77/0.99  --qbf_split                             512
% 3.77/0.99  
% 3.77/0.99  ------ BMC1 Options
% 3.77/0.99  
% 3.77/0.99  --bmc1_incremental                      false
% 3.77/0.99  --bmc1_axioms                           reachable_all
% 3.77/0.99  --bmc1_min_bound                        0
% 3.77/0.99  --bmc1_max_bound                        -1
% 3.77/0.99  --bmc1_max_bound_default                -1
% 3.77/0.99  --bmc1_symbol_reachability              true
% 3.77/0.99  --bmc1_property_lemmas                  false
% 3.77/0.99  --bmc1_k_induction                      false
% 3.77/0.99  --bmc1_non_equiv_states                 false
% 3.77/0.99  --bmc1_deadlock                         false
% 3.77/0.99  --bmc1_ucm                              false
% 3.77/0.99  --bmc1_add_unsat_core                   none
% 3.77/0.99  --bmc1_unsat_core_children              false
% 3.77/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.77/0.99  --bmc1_out_stat                         full
% 3.77/0.99  --bmc1_ground_init                      false
% 3.77/0.99  --bmc1_pre_inst_next_state              false
% 3.77/0.99  --bmc1_pre_inst_state                   false
% 3.77/0.99  --bmc1_pre_inst_reach_state             false
% 3.77/0.99  --bmc1_out_unsat_core                   false
% 3.77/0.99  --bmc1_aig_witness_out                  false
% 3.77/0.99  --bmc1_verbose                          false
% 3.77/0.99  --bmc1_dump_clauses_tptp                false
% 3.77/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.77/0.99  --bmc1_dump_file                        -
% 3.77/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.77/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.77/0.99  --bmc1_ucm_extend_mode                  1
% 3.77/0.99  --bmc1_ucm_init_mode                    2
% 3.77/0.99  --bmc1_ucm_cone_mode                    none
% 3.77/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.77/0.99  --bmc1_ucm_relax_model                  4
% 3.77/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.77/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.77/0.99  --bmc1_ucm_layered_model                none
% 3.77/0.99  --bmc1_ucm_max_lemma_size               10
% 3.77/0.99  
% 3.77/0.99  ------ AIG Options
% 3.77/0.99  
% 3.77/0.99  --aig_mode                              false
% 3.77/0.99  
% 3.77/0.99  ------ Instantiation Options
% 3.77/0.99  
% 3.77/0.99  --instantiation_flag                    true
% 3.77/0.99  --inst_sos_flag                         true
% 3.77/0.99  --inst_sos_phase                        true
% 3.77/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.77/0.99  --inst_lit_sel_side                     none
% 3.77/0.99  --inst_solver_per_active                1400
% 3.77/0.99  --inst_solver_calls_frac                1.
% 3.77/0.99  --inst_passive_queue_type               priority_queues
% 3.77/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.77/0.99  --inst_passive_queues_freq              [25;2]
% 3.77/0.99  --inst_dismatching                      true
% 3.77/0.99  --inst_eager_unprocessed_to_passive     true
% 3.77/0.99  --inst_prop_sim_given                   true
% 3.77/0.99  --inst_prop_sim_new                     false
% 3.77/0.99  --inst_subs_new                         false
% 3.77/0.99  --inst_eq_res_simp                      false
% 3.77/0.99  --inst_subs_given                       false
% 3.77/0.99  --inst_orphan_elimination               true
% 3.77/0.99  --inst_learning_loop_flag               true
% 3.77/0.99  --inst_learning_start                   3000
% 3.77/0.99  --inst_learning_factor                  2
% 3.77/0.99  --inst_start_prop_sim_after_learn       3
% 3.77/0.99  --inst_sel_renew                        solver
% 3.77/0.99  --inst_lit_activity_flag                true
% 3.77/0.99  --inst_restr_to_given                   false
% 3.77/0.99  --inst_activity_threshold               500
% 3.77/0.99  --inst_out_proof                        true
% 3.77/0.99  
% 3.77/0.99  ------ Resolution Options
% 3.77/0.99  
% 3.77/0.99  --resolution_flag                       false
% 3.77/0.99  --res_lit_sel                           adaptive
% 3.77/0.99  --res_lit_sel_side                      none
% 3.77/0.99  --res_ordering                          kbo
% 3.77/0.99  --res_to_prop_solver                    active
% 3.77/0.99  --res_prop_simpl_new                    false
% 3.77/0.99  --res_prop_simpl_given                  true
% 3.77/0.99  --res_passive_queue_type                priority_queues
% 3.77/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.77/0.99  --res_passive_queues_freq               [15;5]
% 3.77/0.99  --res_forward_subs                      full
% 3.77/0.99  --res_backward_subs                     full
% 3.77/0.99  --res_forward_subs_resolution           true
% 3.77/0.99  --res_backward_subs_resolution          true
% 3.77/0.99  --res_orphan_elimination                true
% 3.77/0.99  --res_time_limit                        2.
% 3.77/0.99  --res_out_proof                         true
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Options
% 3.77/0.99  
% 3.77/0.99  --superposition_flag                    true
% 3.77/0.99  --sup_passive_queue_type                priority_queues
% 3.77/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.77/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.77/0.99  --demod_completeness_check              fast
% 3.77/0.99  --demod_use_ground                      true
% 3.77/0.99  --sup_to_prop_solver                    passive
% 3.77/0.99  --sup_prop_simpl_new                    true
% 3.77/0.99  --sup_prop_simpl_given                  true
% 3.77/0.99  --sup_fun_splitting                     true
% 3.77/0.99  --sup_smt_interval                      50000
% 3.77/0.99  
% 3.77/0.99  ------ Superposition Simplification Setup
% 3.77/0.99  
% 3.77/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.77/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.77/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.77/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.77/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_immed_triv                        [TrivRules]
% 3.77/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_immed_bw_main                     []
% 3.77/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.77/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.77/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.77/0.99  --sup_input_bw                          []
% 3.77/0.99  
% 3.77/0.99  ------ Combination Options
% 3.77/0.99  
% 3.77/0.99  --comb_res_mult                         3
% 3.77/0.99  --comb_sup_mult                         2
% 3.77/0.99  --comb_inst_mult                        10
% 3.77/0.99  
% 3.77/0.99  ------ Debug Options
% 3.77/0.99  
% 3.77/0.99  --dbg_backtrace                         false
% 3.77/0.99  --dbg_dump_prop_clauses                 false
% 3.77/0.99  --dbg_dump_prop_clauses_file            -
% 3.77/0.99  --dbg_out_stat                          false
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f30,conjecture,(
% 3.77/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,negated_conjecture,(
% 3.77/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.77/0.99    inference(negated_conjecture,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f64,plain,(
% 3.77/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.77/0.99    inference(ennf_transformation,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f65,plain,(
% 3.77/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.77/0.99    inference(flattening,[],[f64])).
% 3.77/0.99  
% 3.77/0.99  fof(f73,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f72,plain,(
% 3.77/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f74,plain,(
% 3.77/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f73,f72])).
% 3.77/0.99  
% 3.77/0.99  fof(f124,plain,(
% 3.77/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f127,plain,(
% 3.77/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f27,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f60,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.77/0.99    inference(ennf_transformation,[],[f27])).
% 3.77/0.99  
% 3.77/0.99  fof(f61,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.77/0.99    inference(flattening,[],[f60])).
% 3.77/0.99  
% 3.77/0.99  fof(f118,plain,(
% 3.77/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f61])).
% 3.77/0.99  
% 3.77/0.99  fof(f125,plain,(
% 3.77/0.99    v1_funct_1(sK3)),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f22,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f53,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.77/0.99    inference(ennf_transformation,[],[f22])).
% 3.77/0.99  
% 3.77/0.99  fof(f54,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(flattening,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f70,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(nnf_transformation,[],[f54])).
% 3.77/0.99  
% 3.77/0.99  fof(f109,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f70])).
% 3.77/0.99  
% 3.77/0.99  fof(f128,plain,(
% 3.77/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f25,axiom,(
% 3.77/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.77/0.99    inference(pure_predicate_removal,[],[f25])).
% 3.77/0.99  
% 3.77/0.99  fof(f115,plain,(
% 3.77/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f32])).
% 3.77/0.99  
% 3.77/0.99  fof(f122,plain,(
% 3.77/0.99    v1_funct_1(sK2)),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f24,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f57,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.77/0.99    inference(ennf_transformation,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f58,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.77/0.99    inference(flattening,[],[f57])).
% 3.77/0.99  
% 3.77/0.99  fof(f114,plain,(
% 3.77/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f58])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f45,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f92,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f45])).
% 3.77/0.99  
% 3.77/0.99  fof(f15,axiom,(
% 3.77/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f96,plain,(
% 3.77/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.77/0.99    inference(cnf_transformation,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f28,axiom,(
% 3.77/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f119,plain,(
% 3.77/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f28])).
% 3.77/0.99  
% 3.77/0.99  fof(f130,plain,(
% 3.77/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.77/0.99    inference(definition_unfolding,[],[f96,f119])).
% 3.77/0.99  
% 3.77/0.99  fof(f19,axiom,(
% 3.77/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f105,plain,(
% 3.77/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f19])).
% 3.77/0.99  
% 3.77/0.99  fof(f135,plain,(
% 3.77/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.77/0.99    inference(definition_unfolding,[],[f105,f119])).
% 3.77/0.99  
% 3.77/0.99  fof(f29,axiom,(
% 3.77/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f62,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.77/0.99    inference(ennf_transformation,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f63,plain,(
% 3.77/0.99    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.77/0.99    inference(flattening,[],[f62])).
% 3.77/0.99  
% 3.77/0.99  fof(f120,plain,(
% 3.77/0.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f63])).
% 3.77/0.99  
% 3.77/0.99  fof(f123,plain,(
% 3.77/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f126,plain,(
% 3.77/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    v1_xboole_0(k1_xboole_0)),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f75,plain,(
% 3.77/0.99    v1_xboole_0(k1_xboole_0)),
% 3.77/0.99    inference(cnf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f17,axiom,(
% 3.77/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(flattening,[],[f49])).
% 3.77/0.99  
% 3.77/0.99  fof(f100,plain,(
% 3.77/0.99    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f50])).
% 3.77/0.99  
% 3.77/0.99  fof(f16,axiom,(
% 3.77/0.99    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f48,plain,(
% 3.77/0.99    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f97,plain,(
% 3.77/0.99    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f48])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f83,plain,(
% 3.77/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f37])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f36,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f82,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f5,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f35,plain,(
% 3.77/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f5])).
% 3.77/0.99  
% 3.77/0.99  fof(f81,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f35])).
% 3.77/0.99  
% 3.77/0.99  fof(f21,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f52,plain,(
% 3.77/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f21])).
% 3.77/0.99  
% 3.77/0.99  fof(f108,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f52])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f39,plain,(
% 3.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f69,plain,(
% 3.77/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f39])).
% 3.77/0.99  
% 3.77/0.99  fof(f86,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f69])).
% 3.77/0.99  
% 3.77/0.99  fof(f20,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f51,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.77/0.99    inference(ennf_transformation,[],[f20])).
% 3.77/0.99  
% 3.77/0.99  fof(f106,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.77/0.99    inference(cnf_transformation,[],[f51])).
% 3.77/0.99  
% 3.77/0.99  fof(f2,axiom,(
% 3.77/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f66,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f2])).
% 3.77/0.99  
% 3.77/0.99  fof(f67,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(flattening,[],[f66])).
% 3.77/0.99  
% 3.77/0.99  fof(f78,plain,(
% 3.77/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f67])).
% 3.77/0.99  
% 3.77/0.99  fof(f87,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f69])).
% 3.77/0.99  
% 3.77/0.99  fof(f23,axiom,(
% 3.77/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f55,plain,(
% 3.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.77/0.99    inference(ennf_transformation,[],[f23])).
% 3.77/0.99  
% 3.77/0.99  fof(f56,plain,(
% 3.77/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f55])).
% 3.77/0.99  
% 3.77/0.99  fof(f71,plain,(
% 3.77/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f56])).
% 3.77/0.99  
% 3.77/0.99  fof(f112,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f71])).
% 3.77/0.99  
% 3.77/0.99  fof(f142,plain,(
% 3.77/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(equality_resolution,[],[f112])).
% 3.77/0.99  
% 3.77/0.99  fof(f129,plain,(
% 3.77/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.77/0.99    inference(cnf_transformation,[],[f74])).
% 3.77/0.99  
% 3.77/0.99  fof(f77,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.77/0.99    inference(cnf_transformation,[],[f67])).
% 3.77/0.99  
% 3.77/0.99  fof(f139,plain,(
% 3.77/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/0.99    inference(equality_resolution,[],[f77])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_51,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f124]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1694,plain,
% 3.77/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_48,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1697,plain,
% 3.77/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_43,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.77/0.99      | ~ v1_funct_1(X0)
% 3.77/0.99      | ~ v1_funct_1(X3)
% 3.77/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1700,plain,
% 3.77/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.77/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.77/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X5) != iProver_top
% 3.77/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6071,plain,
% 3.77/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X2) != iProver_top
% 3.77/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1697,c_1700]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_50,negated_conjecture,
% 3.77/0.99      ( v1_funct_1(sK3) ),
% 3.77/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_57,plain,
% 3.77/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6437,plain,
% 3.77/0.99      ( v1_funct_1(X2) != iProver_top
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_6071,c_57]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6438,plain,
% 3.77/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.77/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_6437]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6446,plain,
% 3.77/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.77/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1694,c_6438]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_35,plain,
% 3.77/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/0.99      | X3 = X2 ),
% 3.77/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_47,negated_conjecture,
% 3.77/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_567,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/0.99      | X3 = X0
% 3.77/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.77/0.99      | k6_partfun1(sK0) != X3
% 3.77/0.99      | sK0 != X2
% 3.77/0.99      | sK0 != X1 ),
% 3.77/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_47]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_568,plain,
% 3.77/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.77/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.77/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_567]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_40,plain,
% 3.77/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_576,plain,
% 3.77/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.77/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.77/1.00      inference(forward_subsumption_resolution,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_568,c_40]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1690,plain,
% 3.77/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.77/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_53,negated_conjecture,
% 3.77/1.00      ( v1_funct_1(sK2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_38,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.77/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.77/1.00      | ~ v1_funct_1(X0)
% 3.77/1.00      | ~ v1_funct_1(X3) ),
% 3.77/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1775,plain,
% 3.77/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.77/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.77/1.00      | ~ v1_funct_1(sK2)
% 3.77/1.00      | ~ v1_funct_1(sK3) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_38]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2090,plain,
% 3.77/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_1690,c_53,c_51,c_50,c_48,c_576,c_1775]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6449,plain,
% 3.77/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.77/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_6446,c_2090]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_54,plain,
% 3.77/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7115,plain,
% 3.77/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_6449,c_54]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.77/1.00      | ~ v1_relat_1(X1)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1711,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7118,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.77/1.00      | v1_relat_1(sK2) != iProver_top
% 3.77/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_7115,c_1711]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_20,plain,
% 3.77/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f130]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7121,plain,
% 3.77/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.77/1.00      | v1_relat_1(sK2) != iProver_top
% 3.77/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_7118,c_20]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_29,plain,
% 3.77/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f135]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1706,plain,
% 3.77/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_45,plain,
% 3.77/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.77/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.77/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | v2_funct_1(X3)
% 3.77/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.77/1.00      | ~ v1_funct_1(X0)
% 3.77/1.00      | ~ v1_funct_1(X3)
% 3.77/1.00      | k1_xboole_0 = X2 ),
% 3.77/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1698,plain,
% 3.77/1.00      ( k1_xboole_0 = X0
% 3.77/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.77/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.77/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.77/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.77/1.00      | v2_funct_1(X3) = iProver_top
% 3.77/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 3.77/1.00      | v1_funct_1(X1) != iProver_top
% 3.77/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4133,plain,
% 3.77/1.00      ( sK0 = k1_xboole_0
% 3.77/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.77/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.77/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.77/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.77/1.00      | v2_funct_1(sK2) = iProver_top
% 3.77/1.00      | v1_funct_1(sK2) != iProver_top
% 3.77/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2090,c_1698]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_52,negated_conjecture,
% 3.77/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f123]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_55,plain,
% 3.77/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_56,plain,
% 3.77/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_49,negated_conjecture,
% 3.77/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_58,plain,
% 3.77/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_59,plain,
% 3.77/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_181,plain,
% 3.77/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_23,plain,
% 3.77/1.00      ( v2_funct_1(X0)
% 3.77/1.00      | ~ v1_funct_1(X0)
% 3.77/1.00      | ~ v1_relat_1(X0)
% 3.77/1.00      | ~ v1_xboole_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_22,plain,
% 3.77/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8,plain,
% 3.77/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_319,plain,
% 3.77/1.00      ( v2_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_23,c_22,c_8]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1784,plain,
% 3.77/1.00      ( v2_funct_1(sK2) | ~ v1_xboole_0(sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1785,plain,
% 3.77/1.00      ( v2_funct_1(sK2) = iProver_top | v1_xboole_0(sK2) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.77/1.00      | ~ v1_xboole_0(X1)
% 3.77/1.00      | v1_xboole_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1810,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.77/1.00      | ~ v1_xboole_0(X0)
% 3.77/1.00      | v1_xboole_0(sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1879,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.00      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
% 3.77/1.00      | v1_xboole_0(sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1810]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1880,plain,
% 3.77/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.00      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.77/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1879]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1932,plain,
% 3.77/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~ v1_xboole_0(sK0) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1933,plain,
% 3.77/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.77/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1004,plain,
% 3.77/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.77/1.00      theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2015,plain,
% 3.77/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1004]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2016,plain,
% 3.77/1.00      ( sK0 != X0
% 3.77/1.00      | v1_xboole_0(X0) != iProver_top
% 3.77/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2018,plain,
% 3.77/1.00      ( sK0 != k1_xboole_0
% 3.77/1.00      | v1_xboole_0(sK0) = iProver_top
% 3.77/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_2016]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4543,plain,
% 3.77/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.77/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_4133,c_54,c_55,c_56,c_57,c_58,c_59,c_181,c_1785,
% 3.77/1.00                 c_1880,c_1933,c_2018]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4547,plain,
% 3.77/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1706,c_4543]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_32,plain,
% 3.77/1.00      ( v5_relat_1(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_12,plain,
% 3.77/1.00      ( ~ v5_relat_1(X0,X1)
% 3.77/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_644,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_32,c_12]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_31,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_648,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.77/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_644,c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_649,plain,
% 3.77/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.77/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_648]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1687,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2774,plain,
% 3.77/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1697,c_1687]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.77/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1722,plain,
% 3.77/1.00      ( X0 = X1
% 3.77/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4272,plain,
% 3.77/1.00      ( k2_relat_1(sK3) = sK0
% 3.77/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2774,c_1722]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1705,plain,
% 3.77/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3425,plain,
% 3.77/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1697,c_1705]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1844,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.77/1.00      | v1_relat_1(sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2085,plain,
% 3.77/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.77/1.00      | v1_relat_1(sK2) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1844]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2086,plain,
% 3.77/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.77/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2085]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11,plain,
% 3.77/1.00      ( v5_relat_1(X0,X1)
% 3.77/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_36,plain,
% 3.77/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.77/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.77/1.00      | ~ v1_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f142]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_46,negated_conjecture,
% 3.77/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f129]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_585,plain,
% 3.77/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.77/1.00      | ~ v2_funct_1(sK2)
% 3.77/1.00      | ~ v1_relat_1(X0)
% 3.77/1.00      | k2_relat_1(X0) != sK0
% 3.77/1.00      | sK3 != X0 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_46]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_586,plain,
% 3.77/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.77/1.00      | ~ v2_funct_1(sK2)
% 3.77/1.00      | ~ v1_relat_1(sK3)
% 3.77/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_585]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_697,plain,
% 3.77/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.77/1.00      | ~ v2_funct_1(sK2)
% 3.77/1.00      | ~ v1_relat_1(X0)
% 3.77/1.00      | ~ v1_relat_1(sK3)
% 3.77/1.00      | k2_relat_1(sK3) != X1
% 3.77/1.00      | k2_relat_1(sK3) != sK0
% 3.77/1.00      | sK3 != X0 ),
% 3.77/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_586]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_698,plain,
% 3.77/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.77/1.00      | ~ v2_funct_1(sK2)
% 3.77/1.00      | ~ v1_relat_1(sK3)
% 3.77/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.77/1.00      inference(unflattening,[status(thm)],[c_697]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2,plain,
% 3.77/1.00      ( r1_tarski(X0,X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f139]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_708,plain,
% 3.77/1.00      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.77/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_698,c_2]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_712,plain,
% 3.77/1.00      ( k2_relat_1(sK3) != sK0
% 3.77/1.00      | v2_funct_1(sK2) != iProver_top
% 3.77/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_7121,c_4547,c_4272,c_3425,c_2086,c_712,c_56]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ General
% 3.77/1.00  
% 3.77/1.00  abstr_ref_over_cycles:                  0
% 3.77/1.00  abstr_ref_under_cycles:                 0
% 3.77/1.00  gc_basic_clause_elim:                   0
% 3.77/1.00  forced_gc_time:                         0
% 3.77/1.00  parsing_time:                           0.009
% 3.77/1.00  unif_index_cands_time:                  0.
% 3.77/1.00  unif_index_add_time:                    0.
% 3.77/1.00  orderings_time:                         0.
% 3.77/1.00  out_proof_time:                         0.016
% 3.77/1.00  total_time:                             0.317
% 3.77/1.00  num_of_symbols:                         55
% 3.77/1.00  num_of_terms:                           7644
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing
% 3.77/1.00  
% 3.77/1.00  num_of_splits:                          1
% 3.77/1.00  num_of_split_atoms:                     1
% 3.77/1.00  num_of_reused_defs:                     0
% 3.77/1.00  num_eq_ax_congr_red:                    7
% 3.77/1.00  num_of_sem_filtered_clauses:            1
% 3.77/1.00  num_of_subtypes:                        0
% 3.77/1.00  monotx_restored_types:                  0
% 3.77/1.00  sat_num_of_epr_types:                   0
% 3.77/1.00  sat_num_of_non_cyclic_types:            0
% 3.77/1.00  sat_guarded_non_collapsed_types:        0
% 3.77/1.00  num_pure_diseq_elim:                    0
% 3.77/1.00  simp_replaced_by:                       0
% 3.77/1.00  res_preprocessed:                       208
% 3.77/1.00  prep_upred:                             0
% 3.77/1.00  prep_unflattend:                        20
% 3.77/1.00  smt_new_axioms:                         0
% 3.77/1.00  pred_elim_cands:                        7
% 3.77/1.00  pred_elim:                              4
% 3.77/1.00  pred_elim_cl:                           7
% 3.77/1.00  pred_elim_cycles:                       6
% 3.77/1.00  merged_defs:                            0
% 3.77/1.00  merged_defs_ncl:                        0
% 3.77/1.00  bin_hyper_res:                          0
% 3.77/1.00  prep_cycles:                            4
% 3.77/1.00  pred_elim_time:                         0.005
% 3.77/1.00  splitting_time:                         0.
% 3.77/1.00  sem_filter_time:                        0.
% 3.77/1.00  monotx_time:                            0.001
% 3.77/1.00  subtype_inf_time:                       0.
% 3.77/1.00  
% 3.77/1.00  ------ Problem properties
% 3.77/1.00  
% 3.77/1.00  clauses:                                43
% 3.77/1.00  conjectures:                            6
% 3.77/1.00  epr:                                    11
% 3.77/1.00  horn:                                   42
% 3.77/1.00  ground:                                 10
% 3.77/1.00  unary:                                  15
% 3.77/1.00  binary:                                 11
% 3.77/1.00  lits:                                   105
% 3.77/1.00  lits_eq:                                13
% 3.77/1.00  fd_pure:                                0
% 3.77/1.00  fd_pseudo:                              0
% 3.77/1.00  fd_cond:                                3
% 3.77/1.00  fd_pseudo_cond:                         2
% 3.77/1.00  ac_symbols:                             0
% 3.77/1.00  
% 3.77/1.00  ------ Propositional Solver
% 3.77/1.00  
% 3.77/1.00  prop_solver_calls:                      34
% 3.77/1.00  prop_fast_solver_calls:                 1351
% 3.77/1.00  smt_solver_calls:                       0
% 3.77/1.00  smt_fast_solver_calls:                  0
% 3.77/1.00  prop_num_of_clauses:                    3298
% 3.77/1.00  prop_preprocess_simplified:             8685
% 3.77/1.00  prop_fo_subsumed:                       29
% 3.77/1.00  prop_solver_time:                       0.
% 3.77/1.00  smt_solver_time:                        0.
% 3.77/1.00  smt_fast_solver_time:                   0.
% 3.77/1.00  prop_fast_solver_time:                  0.
% 3.77/1.00  prop_unsat_core_time:                   0.
% 3.77/1.00  
% 3.77/1.00  ------ QBF
% 3.77/1.00  
% 3.77/1.00  qbf_q_res:                              0
% 3.77/1.00  qbf_num_tautologies:                    0
% 3.77/1.00  qbf_prep_cycles:                        0
% 3.77/1.00  
% 3.77/1.00  ------ BMC1
% 3.77/1.00  
% 3.77/1.00  bmc1_current_bound:                     -1
% 3.77/1.00  bmc1_last_solved_bound:                 -1
% 3.77/1.00  bmc1_unsat_core_size:                   -1
% 3.77/1.00  bmc1_unsat_core_parents_size:           -1
% 3.77/1.00  bmc1_merge_next_fun:                    0
% 3.77/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.77/1.00  
% 3.77/1.00  ------ Instantiation
% 3.77/1.00  
% 3.77/1.00  inst_num_of_clauses:                    883
% 3.77/1.00  inst_num_in_passive:                    437
% 3.77/1.00  inst_num_in_active:                     445
% 3.77/1.00  inst_num_in_unprocessed:                2
% 3.77/1.00  inst_num_of_loops:                      480
% 3.77/1.00  inst_num_of_learning_restarts:          0
% 3.77/1.00  inst_num_moves_active_passive:          29
% 3.77/1.00  inst_lit_activity:                      0
% 3.77/1.00  inst_lit_activity_moves:                0
% 3.77/1.00  inst_num_tautologies:                   0
% 3.77/1.00  inst_num_prop_implied:                  0
% 3.77/1.00  inst_num_existing_simplified:           0
% 3.77/1.00  inst_num_eq_res_simplified:             0
% 3.77/1.00  inst_num_child_elim:                    0
% 3.77/1.00  inst_num_of_dismatching_blockings:      338
% 3.77/1.00  inst_num_of_non_proper_insts:           1021
% 3.77/1.00  inst_num_of_duplicates:                 0
% 3.77/1.00  inst_inst_num_from_inst_to_res:         0
% 3.77/1.00  inst_dismatching_checking_time:         0.
% 3.77/1.00  
% 3.77/1.00  ------ Resolution
% 3.77/1.00  
% 3.77/1.00  res_num_of_clauses:                     0
% 3.77/1.00  res_num_in_passive:                     0
% 3.77/1.00  res_num_in_active:                      0
% 3.77/1.00  res_num_of_loops:                       212
% 3.77/1.00  res_forward_subset_subsumed:            123
% 3.77/1.00  res_backward_subset_subsumed:           14
% 3.77/1.00  res_forward_subsumed:                   1
% 3.77/1.00  res_backward_subsumed:                  0
% 3.77/1.00  res_forward_subsumption_resolution:     3
% 3.77/1.00  res_backward_subsumption_resolution:    0
% 3.77/1.00  res_clause_to_clause_subsumption:       438
% 3.77/1.00  res_orphan_elimination:                 0
% 3.77/1.00  res_tautology_del:                      76
% 3.77/1.00  res_num_eq_res_simplified:              0
% 3.77/1.00  res_num_sel_changes:                    0
% 3.77/1.00  res_moves_from_active_to_pass:          0
% 3.77/1.00  
% 3.77/1.00  ------ Superposition
% 3.77/1.00  
% 3.77/1.00  sup_time_total:                         0.
% 3.77/1.00  sup_time_generating:                    0.
% 3.77/1.00  sup_time_sim_full:                      0.
% 3.77/1.00  sup_time_sim_immed:                     0.
% 3.77/1.00  
% 3.77/1.00  sup_num_of_clauses:                     162
% 3.77/1.00  sup_num_in_active:                      93
% 3.77/1.00  sup_num_in_passive:                     69
% 3.77/1.00  sup_num_of_loops:                       94
% 3.77/1.00  sup_fw_superposition:                   96
% 3.77/1.00  sup_bw_superposition:                   71
% 3.77/1.00  sup_immediate_simplified:               24
% 3.77/1.00  sup_given_eliminated:                   0
% 3.77/1.00  comparisons_done:                       0
% 3.77/1.00  comparisons_avoided:                    0
% 3.77/1.00  
% 3.77/1.00  ------ Simplifications
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  sim_fw_subset_subsumed:                 10
% 3.77/1.00  sim_bw_subset_subsumed:                 1
% 3.77/1.00  sim_fw_subsumed:                        2
% 3.77/1.00  sim_bw_subsumed:                        1
% 3.77/1.00  sim_fw_subsumption_res:                 0
% 3.77/1.00  sim_bw_subsumption_res:                 0
% 3.77/1.00  sim_tautology_del:                      5
% 3.77/1.00  sim_eq_tautology_del:                   7
% 3.77/1.00  sim_eq_res_simp:                        0
% 3.77/1.00  sim_fw_demodulated:                     6
% 3.77/1.00  sim_bw_demodulated:                     1
% 3.77/1.00  sim_light_normalised:                   10
% 3.77/1.00  sim_joinable_taut:                      0
% 3.77/1.00  sim_joinable_simp:                      0
% 3.77/1.00  sim_ac_normalised:                      0
% 3.77/1.00  sim_smt_subsumption:                    0
% 3.77/1.00  
%------------------------------------------------------------------------------
