%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:17 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 758 expanded)
%              Number of clauses        :  118 ( 234 expanded)
%              Number of leaves         :   27 ( 187 expanded)
%              Depth                    :   20
%              Number of atoms          :  642 (4221 expanded)
%              Number of equality atoms :  227 ( 432 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f53,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f52,f51])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f83])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f70,f83])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f93,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1191,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_23])).

cnf(c_1176,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1236,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1507,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1176,c_38,c_36,c_35,c_33,c_429,c_1236])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1184,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3233,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1507,c_1184])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_86,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_88,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_117,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_121,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_126,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_31,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_438,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_439,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_492,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_439])).

cnf(c_493,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_503,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_3])).

cnf(c_504,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_708,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1249,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1250,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_1252,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1303,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1304,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_1306,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1423,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1424,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_1361,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1465,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_698,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1534,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1535,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1753,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1496,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1833,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_1834,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_1183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_9])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2084,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1175])).

cnf(c_1198,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2445,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1198])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1195,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2564,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1196])).

cnf(c_2570,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_2564])).

cnf(c_1180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2565,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1196])).

cnf(c_3014,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_2565])).

cnf(c_699,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3221,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_3222,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3221])).

cnf(c_3224,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1186,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3382,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1186])).

cnf(c_3414,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3382,c_42])).

cnf(c_3415,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3414])).

cnf(c_3422,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_3415])).

cnf(c_3424,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3422,c_1507])).

cnf(c_3526,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_39])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1192,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3529,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_1192])).

cnf(c_14,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3530,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3529,c_14])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1193,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3528,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_1193])).

cnf(c_15,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3531,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3528,c_15])).

cnf(c_4207,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3531,c_2570,c_3014])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_7])).

cnf(c_1177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_2656,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1177])).

cnf(c_3049,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_3014])).

cnf(c_3053,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1198])).

cnf(c_4212,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_4207,c_3053])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1194,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6309,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_1194])).

cnf(c_6596,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3233,c_39,c_40,c_41,c_42,c_43,c_44,c_88,c_16,c_117,c_121,c_126,c_504,c_1252,c_1306,c_1424,c_1465,c_1535,c_1753,c_1834,c_2445,c_2570,c_3014,c_3224,c_3530,c_6309])).

cnf(c_6600,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1191,c_6596])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:26:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         true
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     num_symb
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       true
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     true
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_input_bw                          []
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 30
% 3.59/0.98  conjectures                             6
% 3.59/0.98  EPR                                     8
% 3.59/0.98  Horn                                    29
% 3.59/0.98  unary                                   15
% 3.59/0.98  binary                                  2
% 3.59/0.98  lits                                    75
% 3.59/0.98  lits eq                                 9
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 2
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Schedule dynamic 5 is on 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    ""
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         true
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     none
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       false
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     true
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_input_bw                          []
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ Proving...
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS status Theorem for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98   Resolution empty clause
% 3.59/0.98  
% 3.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  fof(f13,axiom,(
% 3.59/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f72,plain,(
% 3.59/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f13])).
% 3.59/0.98  
% 3.59/0.98  fof(f20,axiom,(
% 3.59/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f83,plain,(
% 3.59/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f20])).
% 3.59/0.98  
% 3.59/0.98  fof(f97,plain,(
% 3.59/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.59/0.98    inference(definition_unfolding,[],[f72,f83])).
% 3.59/0.98  
% 3.59/0.98  fof(f15,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f33,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.59/0.98    inference(ennf_transformation,[],[f15])).
% 3.59/0.98  
% 3.59/0.98  fof(f34,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(flattening,[],[f33])).
% 3.59/0.98  
% 3.59/0.98  fof(f49,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f34])).
% 3.59/0.98  
% 3.59/0.98  fof(f75,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f22,conjecture,(
% 3.59/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f23,negated_conjecture,(
% 3.59/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.59/0.98    inference(negated_conjecture,[],[f22])).
% 3.59/0.98  
% 3.59/0.98  fof(f43,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.59/0.98    inference(ennf_transformation,[],[f23])).
% 3.59/0.98  
% 3.59/0.98  fof(f44,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.59/0.98    inference(flattening,[],[f43])).
% 3.59/0.98  
% 3.59/0.98  fof(f52,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f51,plain,(
% 3.59/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f53,plain,(
% 3.59/0.98    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f52,f51])).
% 3.59/0.98  
% 3.59/0.98  fof(f92,plain,(
% 3.59/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f16,axiom,(
% 3.59/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f77,plain,(
% 3.59/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f16])).
% 3.59/0.98  
% 3.59/0.98  fof(f99,plain,(
% 3.59/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.59/0.98    inference(definition_unfolding,[],[f77,f83])).
% 3.59/0.98  
% 3.59/0.98  fof(f86,plain,(
% 3.59/0.98    v1_funct_1(sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f88,plain,(
% 3.59/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f89,plain,(
% 3.59/0.98    v1_funct_1(sK3)),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f91,plain,(
% 3.59/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f18,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f37,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.98    inference(ennf_transformation,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f38,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.98    inference(flattening,[],[f37])).
% 3.59/0.98  
% 3.59/0.98  fof(f81,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f38])).
% 3.59/0.98  
% 3.59/0.98  fof(f21,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f41,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.59/0.98    inference(ennf_transformation,[],[f21])).
% 3.59/0.98  
% 3.59/0.98  fof(f42,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.59/0.98    inference(flattening,[],[f41])).
% 3.59/0.98  
% 3.59/0.98  fof(f84,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f87,plain,(
% 3.59/0.98    v1_funct_2(sK2,sK0,sK1)),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f90,plain,(
% 3.59/0.98    v1_funct_2(sK3,sK1,sK0)),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f12,axiom,(
% 3.59/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f70,plain,(
% 3.59/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.59/0.98    inference(cnf_transformation,[],[f12])).
% 3.59/0.98  
% 3.59/0.98  fof(f96,plain,(
% 3.59/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.59/0.98    inference(definition_unfolding,[],[f70,f83])).
% 3.59/0.98  
% 3.59/0.98  fof(f3,axiom,(
% 3.59/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f45,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f3])).
% 3.59/0.98  
% 3.59/0.98  fof(f46,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(flattening,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f56,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f101,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f56])).
% 3.59/0.98  
% 3.59/0.98  fof(f58,plain,(
% 3.59/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f1,axiom,(
% 3.59/0.98    v1_xboole_0(k1_xboole_0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f54,plain,(
% 3.59/0.98    v1_xboole_0(k1_xboole_0)),
% 3.59/0.98    inference(cnf_transformation,[],[f1])).
% 3.59/0.98  
% 3.59/0.98  fof(f6,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f27,plain,(
% 3.59/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f6])).
% 3.59/0.98  
% 3.59/0.98  fof(f48,plain,(
% 3.59/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f27])).
% 3.59/0.98  
% 3.59/0.98  fof(f63,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f17,axiom,(
% 3.59/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f35,plain,(
% 3.59/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.59/0.98    inference(ennf_transformation,[],[f17])).
% 3.59/0.98  
% 3.59/0.98  fof(f36,plain,(
% 3.59/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(flattening,[],[f35])).
% 3.59/0.98  
% 3.59/0.98  fof(f50,plain,(
% 3.59/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f79,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f50])).
% 3.59/0.98  
% 3.59/0.98  fof(f103,plain,(
% 3.59/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f79])).
% 3.59/0.98  
% 3.59/0.98  fof(f93,plain,(
% 3.59/0.98    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.59/0.98    inference(cnf_transformation,[],[f53])).
% 3.59/0.98  
% 3.59/0.98  fof(f57,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f100,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f57])).
% 3.59/0.98  
% 3.59/0.98  fof(f2,axiom,(
% 3.59/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f24,plain,(
% 3.59/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f2])).
% 3.59/0.98  
% 3.59/0.98  fof(f55,plain,(
% 3.59/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f24])).
% 3.59/0.98  
% 3.59/0.98  fof(f14,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f32,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f14])).
% 3.59/0.98  
% 3.59/0.98  fof(f74,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f62,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f7,axiom,(
% 3.59/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f64,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f7])).
% 3.59/0.98  
% 3.59/0.98  fof(f4,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f25,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f4])).
% 3.59/0.98  
% 3.59/0.98  fof(f59,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f25])).
% 3.59/0.98  
% 3.59/0.98  fof(f19,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f39,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.98    inference(ennf_transformation,[],[f19])).
% 3.59/0.98  
% 3.59/0.98  fof(f40,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.98    inference(flattening,[],[f39])).
% 3.59/0.98  
% 3.59/0.98  fof(f82,plain,(
% 3.59/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f40])).
% 3.59/0.98  
% 3.59/0.98  fof(f10,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f31,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f10])).
% 3.59/0.98  
% 3.59/0.98  fof(f67,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f11,axiom,(
% 3.59/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f69,plain,(
% 3.59/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f94,plain,(
% 3.59/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.59/0.98    inference(definition_unfolding,[],[f69,f83])).
% 3.59/0.98  
% 3.59/0.98  fof(f9,axiom,(
% 3.59/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f30,plain,(
% 3.59/0.98    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.59/0.98    inference(ennf_transformation,[],[f9])).
% 3.59/0.98  
% 3.59/0.98  fof(f66,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f30])).
% 3.59/0.98  
% 3.59/0.98  fof(f68,plain,(
% 3.59/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f95,plain,(
% 3.59/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.59/0.98    inference(definition_unfolding,[],[f68,f83])).
% 3.59/0.98  
% 3.59/0.98  fof(f73,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f5,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f26,plain,(
% 3.59/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f5])).
% 3.59/0.98  
% 3.59/0.98  fof(f47,plain,(
% 3.59/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f26])).
% 3.59/0.98  
% 3.59/0.98  fof(f60,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f8,axiom,(
% 3.59/0.98    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f28,plain,(
% 3.59/0.98    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.59/0.98    inference(ennf_transformation,[],[f8])).
% 3.59/0.98  
% 3.59/0.98  fof(f29,plain,(
% 3.59/0.98    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.59/0.98    inference(flattening,[],[f28])).
% 3.59/0.98  
% 3.59/0.98  fof(f65,plain,(
% 3.59/0.98    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  cnf(c_17,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1191,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_22,plain,
% 3.59/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.59/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | X3 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_32,negated_conjecture,
% 3.59/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_420,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | X3 = X0
% 3.59/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.59/0.98      | k6_partfun1(sK0) != X3
% 3.59/0.98      | sK0 != X2
% 3.59/0.98      | sK0 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_421,plain,
% 3.59/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.59/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.59/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_420]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_23,plain,
% 3.59/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_429,plain,
% 3.59/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.59/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.59/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_421,c_23]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1176,plain,
% 3.59/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.59/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_38,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_36,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_35,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_33,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_26,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.59/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1236,plain,
% 3.59/0.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.59/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.59/0.98      | ~ v1_funct_1(sK2)
% 3.59/0.98      | ~ v1_funct_1(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1507,plain,
% 3.59/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_1176,c_38,c_36,c_35,c_33,c_429,c_1236]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_30,plain,
% 3.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3)
% 3.59/0.98      | v2_funct_1(X3)
% 3.59/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1184,plain,
% 3.59/0.98      ( k1_xboole_0 = X0
% 3.59/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.59/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.59/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.59/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.59/0.98      | v1_funct_1(X1) != iProver_top
% 3.59/0.98      | v1_funct_1(X3) != iProver_top
% 3.59/0.98      | v2_funct_1(X3) = iProver_top
% 3.59/0.98      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3233,plain,
% 3.59/0.98      ( sK0 = k1_xboole_0
% 3.59/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.59/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.59/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.59/0.98      | v1_funct_1(sK2) != iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top
% 3.59/0.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.59/0.98      | v2_funct_1(sK2) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1507,c_1184]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_39,plain,
% 3.59/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_37,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_40,plain,
% 3.59/0.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_41,plain,
% 3.59/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_42,plain,
% 3.59/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_34,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_43,plain,
% 3.59/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_44,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_86,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_88,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_86]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_16,plain,
% 3.59/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f101]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_117,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.59/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_121,plain,
% 3.59/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_0,plain,
% 3.59/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_126,plain,
% 3.59/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8,plain,
% 3.59/0.98      ( v5_relat_1(X0,X1) | ~ r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_24,plain,
% 3.59/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_31,negated_conjecture,
% 3.59/0.98      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_438,plain,
% 3.59/0.98      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.59/0.98      | ~ v2_funct_1(sK2)
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | k2_relat_1(X0) != sK0
% 3.59/0.98      | sK3 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_439,plain,
% 3.59/0.98      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.59/0.98      | ~ v2_funct_1(sK2)
% 3.59/0.98      | ~ v1_relat_1(sK3)
% 3.59/0.98      | k2_relat_1(sK3) != sK0 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_438]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_492,plain,
% 3.59/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v2_funct_1(sK2)
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | ~ v1_relat_1(sK3)
% 3.59/0.98      | k2_relat_1(sK3) != X1
% 3.59/0.98      | k2_relat_1(sK3) != sK0
% 3.59/0.98      | sK3 != X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_439]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_493,plain,
% 3.59/0.98      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.59/0.98      | ~ v2_funct_1(sK2)
% 3.59/0.98      | ~ v1_relat_1(sK3)
% 3.59/0.98      | k2_relat_1(sK3) != sK0 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_492]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f100]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_503,plain,
% 3.59/0.98      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.59/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_493,c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_504,plain,
% 3.59/0.98      ( k2_relat_1(sK3) != sK0
% 3.59/0.98      | v2_funct_1(sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_708,plain,
% 3.59/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1249,plain,
% 3.59/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_708]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1250,plain,
% 3.59/0.98      ( sK2 != X0
% 3.59/0.98      | v2_funct_1(X0) != iProver_top
% 3.59/0.98      | v2_funct_1(sK2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1252,plain,
% 3.59/0.98      ( sK2 != k1_xboole_0
% 3.59/0.98      | v2_funct_1(sK2) = iProver_top
% 3.59/0.98      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1250]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1303,plain,
% 3.59/0.98      ( v2_funct_1(X0)
% 3.59/0.98      | ~ v2_funct_1(k6_partfun1(X1))
% 3.59/0.98      | X0 != k6_partfun1(X1) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_708]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1304,plain,
% 3.59/0.98      ( X0 != k6_partfun1(X1)
% 3.59/0.98      | v2_funct_1(X0) = iProver_top
% 3.59/0.98      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1306,plain,
% 3.59/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.59/0.98      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1304]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1,plain,
% 3.59/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1423,plain,
% 3.59/0.98      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1424,plain,
% 3.59/0.98      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1361,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1465,plain,
% 3.59/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1361]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_698,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1534,plain,
% 3.59/0.98      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_698]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1535,plain,
% 3.59/0.98      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1534]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1753,plain,
% 3.59/0.98      ( r1_tarski(sK2,sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1496,plain,
% 3.59/0.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_698]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1833,plain,
% 3.59/0.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1496]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1834,plain,
% 3.59/0.98      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1833]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1183,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_19,plain,
% 3.59/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9,plain,
% 3.59/0.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_459,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_19,c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1175,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2084,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1183,c_1175]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1198,plain,
% 3.59/0.98      ( X0 = X1
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.59/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2445,plain,
% 3.59/0.98      ( k2_relat_1(sK3) = sK0
% 3.59/0.98      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2084,c_1198]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1195,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1196,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2564,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1183,c_1196]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2570,plain,
% 3.59/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1195,c_2564]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1180,plain,
% 3.59/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2565,plain,
% 3.59/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.59/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1180,c_1196]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3014,plain,
% 3.59/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1195,c_2565]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_699,plain,
% 3.59/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3221,plain,
% 3.59/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_699]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3222,plain,
% 3.59/0.98      ( sK0 != X0
% 3.59/0.98      | v1_xboole_0(X0) != iProver_top
% 3.59/0.98      | v1_xboole_0(sK0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_3221]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3224,plain,
% 3.59/0.98      ( sK0 != k1_xboole_0
% 3.59/0.98      | v1_xboole_0(sK0) = iProver_top
% 3.59/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3222]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_28,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(X3)
% 3.59/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1186,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.59/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.59/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X5) != iProver_top
% 3.59/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3382,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X2) != iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1183,c_1186]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3414,plain,
% 3.59/0.98      ( v1_funct_1(X2) != iProver_top
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3382,c_42]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3415,plain,
% 3.59/0.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_3414]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3422,plain,
% 3.59/0.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.59/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1180,c_3415]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3424,plain,
% 3.59/0.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.59/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_3422,c_1507]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3526,plain,
% 3.59/0.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3424,c_39]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_13,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | ~ v1_relat_1(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1192,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3529,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3526,c_1192]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_14,plain,
% 3.59/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3530,plain,
% 3.59/0.98      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_3529,c_14]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | ~ v1_relat_1(X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1193,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top
% 3.59/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3528,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3526,c_1193]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_15,plain,
% 3.59/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3531,plain,
% 3.59/0.98      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.59/0.98      | v1_relat_1(sK2) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_3528,c_15]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4207,plain,
% 3.59/0.98      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_3531,c_2570,c_3014]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_20,plain,
% 3.59/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7,plain,
% 3.59/0.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_399,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_20,c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1177,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2656,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.59/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1180,c_1177]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3049,plain,
% 3.59/0.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2656,c_3014]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3053,plain,
% 3.59/0.98      ( k1_relat_1(sK2) = sK0 | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_3049,c_1198]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4212,plain,
% 3.59/0.98      ( k1_relat_1(sK2) = sK0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4207,c_3053]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11,plain,
% 3.59/0.98      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1194,plain,
% 3.59/0.98      ( v1_relat_1(X0) != iProver_top
% 3.59/0.98      | v1_xboole_0(X0) = iProver_top
% 3.59/0.98      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6309,plain,
% 3.59/0.98      ( v1_relat_1(sK2) != iProver_top
% 3.59/0.98      | v1_xboole_0(sK2) = iProver_top
% 3.59/0.98      | v1_xboole_0(sK0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4212,c_1194]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6596,plain,
% 3.59/0.98      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_3233,c_39,c_40,c_41,c_42,c_43,c_44,c_88,c_16,c_117,c_121,
% 3.59/0.98                 c_126,c_504,c_1252,c_1306,c_1424,c_1465,c_1535,c_1753,
% 3.59/0.98                 c_1834,c_2445,c_2570,c_3014,c_3224,c_3530,c_6309]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6600,plain,
% 3.59/0.98      ( $false ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_1191,c_6596]) ).
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  ------                               Statistics
% 3.59/0.98  
% 3.59/0.98  ------ General
% 3.59/0.98  
% 3.59/0.98  abstr_ref_over_cycles:                  0
% 3.59/0.98  abstr_ref_under_cycles:                 0
% 3.59/0.98  gc_basic_clause_elim:                   0
% 3.59/0.98  forced_gc_time:                         0
% 3.59/0.98  parsing_time:                           0.007
% 3.59/0.98  unif_index_cands_time:                  0.
% 3.59/0.98  unif_index_add_time:                    0.
% 3.59/0.98  orderings_time:                         0.
% 3.59/0.98  out_proof_time:                         0.011
% 3.59/0.98  total_time:                             0.255
% 3.59/0.98  num_of_symbols:                         54
% 3.59/0.98  num_of_terms:                           10760
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing
% 3.59/0.98  
% 3.59/0.98  num_of_splits:                          0
% 3.59/0.98  num_of_split_atoms:                     0
% 3.59/0.98  num_of_reused_defs:                     0
% 3.59/0.98  num_eq_ax_congr_red:                    9
% 3.59/0.98  num_of_sem_filtered_clauses:            1
% 3.59/0.98  num_of_subtypes:                        0
% 3.59/0.98  monotx_restored_types:                  0
% 3.59/0.98  sat_num_of_epr_types:                   0
% 3.59/0.99  sat_num_of_non_cyclic_types:            0
% 3.59/0.99  sat_guarded_non_collapsed_types:        0
% 3.59/0.99  num_pure_diseq_elim:                    0
% 3.59/0.99  simp_replaced_by:                       0
% 3.59/0.99  res_preprocessed:                       159
% 3.59/0.99  prep_upred:                             0
% 3.59/0.99  prep_unflattend:                        15
% 3.59/0.99  smt_new_axioms:                         0
% 3.59/0.99  pred_elim_cands:                        7
% 3.59/0.99  pred_elim:                              4
% 3.59/0.99  pred_elim_cl:                           8
% 3.59/0.99  pred_elim_cycles:                       6
% 3.59/0.99  merged_defs:                            0
% 3.59/0.99  merged_defs_ncl:                        0
% 3.59/0.99  bin_hyper_res:                          0
% 3.59/0.99  prep_cycles:                            4
% 3.59/0.99  pred_elim_time:                         0.004
% 3.59/0.99  splitting_time:                         0.
% 3.59/0.99  sem_filter_time:                        0.
% 3.59/0.99  monotx_time:                            0.001
% 3.59/0.99  subtype_inf_time:                       0.
% 3.59/0.99  
% 3.59/0.99  ------ Problem properties
% 3.59/0.99  
% 3.59/0.99  clauses:                                30
% 3.59/0.99  conjectures:                            6
% 3.59/0.99  epr:                                    8
% 3.59/0.99  horn:                                   29
% 3.59/0.99  ground:                                 10
% 3.59/0.99  unary:                                  15
% 3.59/0.99  binary:                                 2
% 3.59/0.99  lits:                                   75
% 3.59/0.99  lits_eq:                                9
% 3.59/0.99  fd_pure:                                0
% 3.59/0.99  fd_pseudo:                              0
% 3.59/0.99  fd_cond:                                2
% 3.59/0.99  fd_pseudo_cond:                         1
% 3.59/0.99  ac_symbols:                             0
% 3.59/0.99  
% 3.59/0.99  ------ Propositional Solver
% 3.59/0.99  
% 3.59/0.99  prop_solver_calls:                      33
% 3.59/0.99  prop_fast_solver_calls:                 1146
% 3.59/0.99  smt_solver_calls:                       0
% 3.59/0.99  smt_fast_solver_calls:                  0
% 3.59/0.99  prop_num_of_clauses:                    3322
% 3.59/0.99  prop_preprocess_simplified:             8320
% 3.59/0.99  prop_fo_subsumed:                       59
% 3.59/0.99  prop_solver_time:                       0.
% 3.59/0.99  smt_solver_time:                        0.
% 3.59/0.99  smt_fast_solver_time:                   0.
% 3.59/0.99  prop_fast_solver_time:                  0.
% 3.59/0.99  prop_unsat_core_time:                   0.
% 3.59/0.99  
% 3.59/0.99  ------ QBF
% 3.59/0.99  
% 3.59/0.99  qbf_q_res:                              0
% 3.59/0.99  qbf_num_tautologies:                    0
% 3.59/0.99  qbf_prep_cycles:                        0
% 3.59/0.99  
% 3.59/0.99  ------ BMC1
% 3.59/0.99  
% 3.59/0.99  bmc1_current_bound:                     -1
% 3.59/0.99  bmc1_last_solved_bound:                 -1
% 3.59/0.99  bmc1_unsat_core_size:                   -1
% 3.59/0.99  bmc1_unsat_core_parents_size:           -1
% 3.59/0.99  bmc1_merge_next_fun:                    0
% 3.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation
% 3.59/0.99  
% 3.59/0.99  inst_num_of_clauses:                    905
% 3.59/0.99  inst_num_in_passive:                    253
% 3.59/0.99  inst_num_in_active:                     458
% 3.59/0.99  inst_num_in_unprocessed:                194
% 3.59/0.99  inst_num_of_loops:                      490
% 3.59/0.99  inst_num_of_learning_restarts:          0
% 3.59/0.99  inst_num_moves_active_passive:          27
% 3.59/0.99  inst_lit_activity:                      0
% 3.59/0.99  inst_lit_activity_moves:                0
% 3.59/0.99  inst_num_tautologies:                   0
% 3.59/0.99  inst_num_prop_implied:                  0
% 3.59/0.99  inst_num_existing_simplified:           0
% 3.59/0.99  inst_num_eq_res_simplified:             0
% 3.59/0.99  inst_num_child_elim:                    0
% 3.59/0.99  inst_num_of_dismatching_blockings:      196
% 3.59/0.99  inst_num_of_non_proper_insts:           1030
% 3.59/0.99  inst_num_of_duplicates:                 0
% 3.59/0.99  inst_inst_num_from_inst_to_res:         0
% 3.59/0.99  inst_dismatching_checking_time:         0.
% 3.59/0.99  
% 3.59/0.99  ------ Resolution
% 3.59/0.99  
% 3.59/0.99  res_num_of_clauses:                     0
% 3.59/0.99  res_num_in_passive:                     0
% 3.59/0.99  res_num_in_active:                      0
% 3.59/0.99  res_num_of_loops:                       163
% 3.59/0.99  res_forward_subset_subsumed:            88
% 3.59/0.99  res_backward_subset_subsumed:           0
% 3.59/0.99  res_forward_subsumed:                   0
% 3.59/0.99  res_backward_subsumed:                  1
% 3.59/0.99  res_forward_subsumption_resolution:     2
% 3.59/0.99  res_backward_subsumption_resolution:    0
% 3.59/0.99  res_clause_to_clause_subsumption:       316
% 3.59/0.99  res_orphan_elimination:                 0
% 3.59/0.99  res_tautology_del:                      81
% 3.59/0.99  res_num_eq_res_simplified:              0
% 3.59/0.99  res_num_sel_changes:                    0
% 3.59/0.99  res_moves_from_active_to_pass:          0
% 3.59/0.99  
% 3.59/0.99  ------ Superposition
% 3.59/0.99  
% 3.59/0.99  sup_time_total:                         0.
% 3.59/0.99  sup_time_generating:                    0.
% 3.59/0.99  sup_time_sim_full:                      0.
% 3.59/0.99  sup_time_sim_immed:                     0.
% 3.59/0.99  
% 3.59/0.99  sup_num_of_clauses:                     139
% 3.59/0.99  sup_num_in_active:                      83
% 3.59/0.99  sup_num_in_passive:                     56
% 3.59/0.99  sup_num_of_loops:                       96
% 3.59/0.99  sup_fw_superposition:                   78
% 3.59/0.99  sup_bw_superposition:                   70
% 3.59/0.99  sup_immediate_simplified:               43
% 3.59/0.99  sup_given_eliminated:                   1
% 3.59/0.99  comparisons_done:                       0
% 3.59/0.99  comparisons_avoided:                    0
% 3.59/0.99  
% 3.59/0.99  ------ Simplifications
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  sim_fw_subset_subsumed:                 3
% 3.59/0.99  sim_bw_subset_subsumed:                 14
% 3.59/0.99  sim_fw_subsumed:                        9
% 3.59/0.99  sim_bw_subsumed:                        2
% 3.59/0.99  sim_fw_subsumption_res:                 0
% 3.59/0.99  sim_bw_subsumption_res:                 0
% 3.59/0.99  sim_tautology_del:                      2
% 3.59/0.99  sim_eq_tautology_del:                   9
% 3.59/0.99  sim_eq_res_simp:                        1
% 3.59/0.99  sim_fw_demodulated:                     2
% 3.59/0.99  sim_bw_demodulated:                     5
% 3.59/0.99  sim_light_normalised:                   30
% 3.59/0.99  sim_joinable_taut:                      0
% 3.59/0.99  sim_joinable_simp:                      0
% 3.59/0.99  sim_ac_normalised:                      0
% 3.59/0.99  sim_smt_subsumption:                    0
% 3.59/0.99  
%------------------------------------------------------------------------------
