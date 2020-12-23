%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:01 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  191 (1309 expanded)
%              Number of clauses        :  115 ( 430 expanded)
%              Number of leaves         :   22 ( 311 expanded)
%              Depth                    :   23
%              Number of atoms          :  597 (8057 expanded)
%              Number of equality atoms :  187 ( 629 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f95,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK6,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK6),k6_partfun1(X0))
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK6,X1,X0)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
          ( ( ~ v2_funct_2(X3,sK3)
            | ~ v2_funct_1(sK5) )
          & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,X3),k6_partfun1(sK3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
          & v1_funct_2(X3,sK4,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ v2_funct_2(sK6,sK3)
      | ~ v2_funct_1(sK5) )
    & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    & v1_funct_2(sK6,sK4,sK3)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f44,f56,f55])).

fof(f93,plain,(
    r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

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

fof(f85,plain,(
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

fof(f88,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,
    ( ~ v2_funct_2(sK6,sK3)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1136,plain,
    ( r2_hidden(sK0(X0_55),X0_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1759,plain,
    ( r2_hidden(sK0(X0_55),X0_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1110,plain,
    ( ~ r2_hidden(X0_57,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_411])).

cnf(c_1785,plain,
    ( r2_hidden(X0_57,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_2872,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1785])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1133,plain,
    ( ~ v1_xboole_0(X0_55)
    | v1_xboole_0(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1762,plain,
    ( v1_xboole_0(X0_55) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1121,plain,
    ( m1_subset_1(k6_partfun1(X0_55),k1_zfmisc_1(k2_zfmisc_1(X0_55,X0_55))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1774,plain,
    ( m1_subset_1(k6_partfun1(X0_55),k1_zfmisc_1(k2_zfmisc_1(X0_55,X0_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_57,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1763,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | r2_hidden(X0_57,X0_55) != iProver_top
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_2636,plain,
    ( r2_hidden(X0_57,k6_partfun1(X0_55)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0_55,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1763])).

cnf(c_5426,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0_55,X0_55)) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_55)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_2636])).

cnf(c_5478,plain,
    ( v1_xboole_0(X0_55) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_55)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_5426])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1134,plain,
    ( ~ v1_xboole_0(X0_55)
    | k1_xboole_0 = X0_55 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1761,plain,
    ( k1_xboole_0 = X0_55
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_5497,plain,
    ( k6_partfun1(X0_55) = k1_xboole_0
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_5478,c_1761])).

cnf(c_6489,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2872,c_5497])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1125,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1770,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_7420,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6489,c_1770])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1120,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X5_55)))
    | m1_subset_1(k1_partfun1(X4_55,X5_55,X1_55,X2_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1775,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X5_55))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_55,X5_55,X1_55,X2_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) = iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) != X0
    | k6_partfun1(sK3) != X3
    | sK3 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_523,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_66,plain,
    ( m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_66])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_1789,plain,
    ( k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_4517,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1789])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4606,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4517,c_36,c_38,c_39,c_41])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1117,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v2_funct_1(X3_55)
    | ~ v2_funct_1(k1_partfun1(X4_55,X1_55,X1_55,X2_55,X3_55,X0_55))
    | k1_xboole_0 = X2_55 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1778,plain,
    ( k1_xboole_0 = X0_55
    | v1_funct_2(X1_55,X2_55,X0_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X0_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v2_funct_1(X3_55) = iProver_top
    | v2_funct_1(k1_partfun1(X4_55,X2_55,X2_55,X0_55,X3_55,X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_4632,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(k6_partfun1(sK3)) != iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4606,c_1778])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_89,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_91,plain,
    ( v2_funct_1(k6_partfun1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_1116,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1779,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | k2_relset_1(X1_55,X2_55,X0_55) = k2_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1773,plain,
    ( k2_relset_1(X0_55,X1_55,X2_55) = k2_relat_1(X2_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_3156,plain,
    ( k2_relset_1(sK4,sK3,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1779,c_1773])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_537,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ v1_funct_2(X2,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X1,sK3,X0) = sK3
    | k6_partfun1(sK3) != k6_partfun1(sK3) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_779,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ v1_funct_2(X2,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X1,sK3,X0) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_537])).

cnf(c_1106,plain,
    ( ~ v1_funct_2(X0_55,X1_55,sK3)
    | ~ v1_funct_2(X2_55,sK3,X1_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3)))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X2_55)
    | k1_partfun1(sK3,X1_55,X1_55,sK3,X2_55,X0_55) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X1_55,sK3,X0_55) = sK3 ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_1790,plain,
    ( k1_partfun1(sK3,X0_55,X0_55,sK3,X1_55,X2_55) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
    | k2_relset_1(X0_55,sK3,X2_55) = sK3
    | v1_funct_2(X2_55,X0_55,sK3) != iProver_top
    | v1_funct_2(X1_55,sK3,X0_55) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_2479,plain,
    ( k2_relset_1(sK4,sK3,sK6) = sK3
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1790])).

cnf(c_2482,plain,
    ( k2_relset_1(sK4,sK3,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2479,c_36,c_37,c_38,c_39,c_40,c_41])).

cnf(c_3164,plain,
    ( k2_relat_1(sK6) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3156,c_2482])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_440,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_441,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_451,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_441,c_15])).

cnf(c_28,negated_conjecture,
    ( ~ v2_funct_2(sK6,sK3)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK5)
    | k2_relat_1(X0) != sK3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_451,c_28])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
    | ~ v2_funct_1(sK5)
    | k2_relat_1(sK6) != sK3 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6))))
    | ~ v2_funct_1(sK5)
    | k2_relat_1(sK6) != sK3 ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_1138,plain,
    ( ~ v2_funct_1(sK5)
    | sP0_iProver_split
    | k2_relat_1(sK6) != sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1109])).

cnf(c_1786,plain,
    ( k2_relat_1(sK6) != sK3
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_3294,plain,
    ( sK3 != sK3
    | v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_1786])).

cnf(c_3295,plain,
    ( v2_funct_1(sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3294])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1109])).

cnf(c_1787,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_3293,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_3164,c_1787])).

cnf(c_3619,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_3293])).

cnf(c_4715,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4632,c_36,c_37,c_38,c_39,c_40,c_41,c_91,c_3295,c_3619])).

cnf(c_1113,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1782,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_2635,plain,
    ( r2_hidden(X0_57,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1782,c_1763])).

cnf(c_4725,plain,
    ( r2_hidden(X0_57,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4715,c_2635])).

cnf(c_2233,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_2235,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2234,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_2237,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2234])).

cnf(c_1147,plain,
    ( ~ v1_xboole_0(X0_55)
    | v1_xboole_0(X1_55)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_2660,plain,
    ( v1_xboole_0(X0_55)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_55 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_2665,plain,
    ( X0_55 != k1_xboole_0
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2660])).

cnf(c_2667,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2665])).

cnf(c_3288,plain,
    ( r2_hidden(X0_57,sK5) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_2635])).

cnf(c_4982,plain,
    ( r2_hidden(X0_57,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4725,c_36,c_37,c_38,c_39,c_40,c_41,c_91,c_2235,c_2237,c_2667,c_3288,c_3295,c_3619,c_4632])).

cnf(c_4989,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_4982])).

cnf(c_5085,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4989,c_1761])).

cnf(c_3782,plain,
    ( v2_funct_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3295,c_3619])).

cnf(c_5165,plain,
    ( v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5085,c_3782])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7420,c_5165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:49:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.35/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/0.98  
% 3.35/0.98  ------  iProver source info
% 3.35/0.98  
% 3.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/0.98  git: non_committed_changes: false
% 3.35/0.98  git: last_make_outside_of_git: false
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    --mode clausify
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.98  --bmc1_non_equiv_states                 false
% 3.35/0.98  --bmc1_deadlock                         false
% 3.35/0.98  --bmc1_ucm                              false
% 3.35/0.98  --bmc1_add_unsat_core                   none
% 3.35/0.98  --bmc1_unsat_core_children              false
% 3.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.98  --bmc1_out_stat                         full
% 3.35/0.98  --bmc1_ground_init                      false
% 3.35/0.98  --bmc1_pre_inst_next_state              false
% 3.35/0.98  --bmc1_pre_inst_state                   false
% 3.35/0.98  --bmc1_pre_inst_reach_state             false
% 3.35/0.98  --bmc1_out_unsat_core                   false
% 3.35/0.98  --bmc1_aig_witness_out                  false
% 3.35/0.98  --bmc1_verbose                          false
% 3.35/0.98  --bmc1_dump_clauses_tptp                false
% 3.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.98  --bmc1_dump_file                        -
% 3.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.98  --bmc1_ucm_extend_mode                  1
% 3.35/0.98  --bmc1_ucm_init_mode                    2
% 3.35/0.98  --bmc1_ucm_cone_mode                    none
% 3.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.98  --bmc1_ucm_relax_model                  4
% 3.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.98  --bmc1_ucm_layered_model                none
% 3.35/0.98  --bmc1_ucm_max_lemma_size               10
% 3.35/0.98  
% 3.35/0.98  ------ AIG Options
% 3.35/0.98  
% 3.35/0.98  --aig_mode                              false
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation Options
% 3.35/0.98  
% 3.35/0.98  --instantiation_flag                    true
% 3.35/0.98  --inst_sos_flag                         false
% 3.35/0.98  --inst_sos_phase                        true
% 3.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel_side                     num_symb
% 3.35/0.98  --inst_solver_per_active                1400
% 3.35/0.98  --inst_solver_calls_frac                1.
% 3.35/0.98  --inst_passive_queue_type               priority_queues
% 3.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.98  --inst_passive_queues_freq              [25;2]
% 3.35/0.98  --inst_dismatching                      true
% 3.35/0.98  --inst_eager_unprocessed_to_passive     true
% 3.35/0.98  --inst_prop_sim_given                   true
% 3.35/0.98  --inst_prop_sim_new                     false
% 3.35/0.98  --inst_subs_new                         false
% 3.35/0.98  --inst_eq_res_simp                      false
% 3.35/0.98  --inst_subs_given                       false
% 3.35/0.98  --inst_orphan_elimination               true
% 3.35/0.98  --inst_learning_loop_flag               true
% 3.35/0.98  --inst_learning_start                   3000
% 3.35/0.98  --inst_learning_factor                  2
% 3.35/0.98  --inst_start_prop_sim_after_learn       3
% 3.35/0.98  --inst_sel_renew                        solver
% 3.35/0.98  --inst_lit_activity_flag                true
% 3.35/0.98  --inst_restr_to_given                   false
% 3.35/0.98  --inst_activity_threshold               500
% 3.35/0.98  --inst_out_proof                        true
% 3.35/0.98  
% 3.35/0.98  ------ Resolution Options
% 3.35/0.98  
% 3.35/0.98  --resolution_flag                       true
% 3.35/0.98  --res_lit_sel                           adaptive
% 3.35/0.98  --res_lit_sel_side                      none
% 3.35/0.98  --res_ordering                          kbo
% 3.35/0.98  --res_to_prop_solver                    active
% 3.35/0.98  --res_prop_simpl_new                    false
% 3.35/0.98  --res_prop_simpl_given                  true
% 3.35/0.98  --res_passive_queue_type                priority_queues
% 3.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.98  --res_passive_queues_freq               [15;5]
% 3.35/0.98  --res_forward_subs                      full
% 3.35/0.98  --res_backward_subs                     full
% 3.35/0.98  --res_forward_subs_resolution           true
% 3.35/0.98  --res_backward_subs_resolution          true
% 3.35/0.98  --res_orphan_elimination                true
% 3.35/0.98  --res_time_limit                        2.
% 3.35/0.98  --res_out_proof                         true
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Options
% 3.35/0.98  
% 3.35/0.98  --superposition_flag                    true
% 3.35/0.98  --sup_passive_queue_type                priority_queues
% 3.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.98  --demod_completeness_check              fast
% 3.35/0.98  --demod_use_ground                      true
% 3.35/0.98  --sup_to_prop_solver                    passive
% 3.35/0.98  --sup_prop_simpl_new                    true
% 3.35/0.98  --sup_prop_simpl_given                  true
% 3.35/0.98  --sup_fun_splitting                     false
% 3.35/0.98  --sup_smt_interval                      50000
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Simplification Setup
% 3.35/0.98  
% 3.35/0.98  --sup_indices_passive                   []
% 3.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_full_bw                           [BwDemod]
% 3.35/0.98  --sup_immed_triv                        [TrivRules]
% 3.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_immed_bw_main                     []
% 3.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  
% 3.35/0.98  ------ Combination Options
% 3.35/0.98  
% 3.35/0.98  --comb_res_mult                         3
% 3.35/0.98  --comb_sup_mult                         2
% 3.35/0.98  --comb_inst_mult                        10
% 3.35/0.98  
% 3.35/0.98  ------ Debug Options
% 3.35/0.98  
% 3.35/0.98  --dbg_backtrace                         false
% 3.35/0.98  --dbg_dump_prop_clauses                 false
% 3.35/0.98  --dbg_dump_prop_clauses_file            -
% 3.35/0.98  --dbg_out_stat                          false
% 3.35/0.98  ------ Parsing...
% 3.35/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.35/0.98  ------ Proving...
% 3.35/0.98  ------ Problem Properties 
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  clauses                                 32
% 3.35/0.98  conjectures                             6
% 3.35/0.98  EPR                                     7
% 3.35/0.98  Horn                                    27
% 3.35/0.98  unary                                   10
% 3.35/0.98  binary                                  9
% 3.35/0.98  lits                                    100
% 3.35/0.98  lits eq                                 13
% 3.35/0.98  fd_pure                                 0
% 3.35/0.98  fd_pseudo                               0
% 3.35/0.98  fd_cond                                 2
% 3.35/0.98  fd_pseudo_cond                          1
% 3.35/0.98  AC symbols                              0
% 3.35/0.98  
% 3.35/0.98  ------ Schedule dynamic 5 is on 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  ------ 
% 3.35/0.98  Current options:
% 3.35/0.98  ------ 
% 3.35/0.98  
% 3.35/0.98  ------ Input Options
% 3.35/0.98  
% 3.35/0.98  --out_options                           all
% 3.35/0.98  --tptp_safe_out                         true
% 3.35/0.98  --problem_path                          ""
% 3.35/0.98  --include_path                          ""
% 3.35/0.98  --clausifier                            res/vclausify_rel
% 3.35/0.98  --clausifier_options                    --mode clausify
% 3.35/0.98  --stdin                                 false
% 3.35/0.98  --stats_out                             all
% 3.35/0.98  
% 3.35/0.98  ------ General Options
% 3.35/0.98  
% 3.35/0.98  --fof                                   false
% 3.35/0.98  --time_out_real                         305.
% 3.35/0.98  --time_out_virtual                      -1.
% 3.35/0.98  --symbol_type_check                     false
% 3.35/0.98  --clausify_out                          false
% 3.35/0.98  --sig_cnt_out                           false
% 3.35/0.98  --trig_cnt_out                          false
% 3.35/0.98  --trig_cnt_out_tolerance                1.
% 3.35/0.98  --trig_cnt_out_sk_spl                   false
% 3.35/0.98  --abstr_cl_out                          false
% 3.35/0.98  
% 3.35/0.98  ------ Global Options
% 3.35/0.98  
% 3.35/0.98  --schedule                              default
% 3.35/0.98  --add_important_lit                     false
% 3.35/0.98  --prop_solver_per_cl                    1000
% 3.35/0.98  --min_unsat_core                        false
% 3.35/0.98  --soft_assumptions                      false
% 3.35/0.98  --soft_lemma_size                       3
% 3.35/0.98  --prop_impl_unit_size                   0
% 3.35/0.98  --prop_impl_unit                        []
% 3.35/0.98  --share_sel_clauses                     true
% 3.35/0.98  --reset_solvers                         false
% 3.35/0.98  --bc_imp_inh                            [conj_cone]
% 3.35/0.98  --conj_cone_tolerance                   3.
% 3.35/0.98  --extra_neg_conj                        none
% 3.35/0.98  --large_theory_mode                     true
% 3.35/0.98  --prolific_symb_bound                   200
% 3.35/0.98  --lt_threshold                          2000
% 3.35/0.98  --clause_weak_htbl                      true
% 3.35/0.98  --gc_record_bc_elim                     false
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing Options
% 3.35/0.98  
% 3.35/0.98  --preprocessing_flag                    true
% 3.35/0.98  --time_out_prep_mult                    0.1
% 3.35/0.98  --splitting_mode                        input
% 3.35/0.98  --splitting_grd                         true
% 3.35/0.98  --splitting_cvd                         false
% 3.35/0.98  --splitting_cvd_svl                     false
% 3.35/0.98  --splitting_nvd                         32
% 3.35/0.98  --sub_typing                            true
% 3.35/0.98  --prep_gs_sim                           true
% 3.35/0.98  --prep_unflatten                        true
% 3.35/0.98  --prep_res_sim                          true
% 3.35/0.98  --prep_upred                            true
% 3.35/0.98  --prep_sem_filter                       exhaustive
% 3.35/0.98  --prep_sem_filter_out                   false
% 3.35/0.98  --pred_elim                             true
% 3.35/0.98  --res_sim_input                         true
% 3.35/0.98  --eq_ax_congr_red                       true
% 3.35/0.98  --pure_diseq_elim                       true
% 3.35/0.98  --brand_transform                       false
% 3.35/0.98  --non_eq_to_eq                          false
% 3.35/0.98  --prep_def_merge                        true
% 3.35/0.98  --prep_def_merge_prop_impl              false
% 3.35/0.98  --prep_def_merge_mbd                    true
% 3.35/0.98  --prep_def_merge_tr_red                 false
% 3.35/0.98  --prep_def_merge_tr_cl                  false
% 3.35/0.98  --smt_preprocessing                     true
% 3.35/0.98  --smt_ac_axioms                         fast
% 3.35/0.98  --preprocessed_out                      false
% 3.35/0.98  --preprocessed_stats                    false
% 3.35/0.98  
% 3.35/0.98  ------ Abstraction refinement Options
% 3.35/0.98  
% 3.35/0.98  --abstr_ref                             []
% 3.35/0.98  --abstr_ref_prep                        false
% 3.35/0.98  --abstr_ref_until_sat                   false
% 3.35/0.98  --abstr_ref_sig_restrict                funpre
% 3.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.35/0.98  --abstr_ref_under                       []
% 3.35/0.98  
% 3.35/0.98  ------ SAT Options
% 3.35/0.98  
% 3.35/0.98  --sat_mode                              false
% 3.35/0.98  --sat_fm_restart_options                ""
% 3.35/0.98  --sat_gr_def                            false
% 3.35/0.98  --sat_epr_types                         true
% 3.35/0.98  --sat_non_cyclic_types                  false
% 3.35/0.98  --sat_finite_models                     false
% 3.35/0.98  --sat_fm_lemmas                         false
% 3.35/0.98  --sat_fm_prep                           false
% 3.35/0.98  --sat_fm_uc_incr                        true
% 3.35/0.98  --sat_out_model                         small
% 3.35/0.98  --sat_out_clauses                       false
% 3.35/0.98  
% 3.35/0.98  ------ QBF Options
% 3.35/0.98  
% 3.35/0.98  --qbf_mode                              false
% 3.35/0.98  --qbf_elim_univ                         false
% 3.35/0.98  --qbf_dom_inst                          none
% 3.35/0.98  --qbf_dom_pre_inst                      false
% 3.35/0.98  --qbf_sk_in                             false
% 3.35/0.98  --qbf_pred_elim                         true
% 3.35/0.98  --qbf_split                             512
% 3.35/0.98  
% 3.35/0.98  ------ BMC1 Options
% 3.35/0.98  
% 3.35/0.98  --bmc1_incremental                      false
% 3.35/0.98  --bmc1_axioms                           reachable_all
% 3.35/0.98  --bmc1_min_bound                        0
% 3.35/0.98  --bmc1_max_bound                        -1
% 3.35/0.98  --bmc1_max_bound_default                -1
% 3.35/0.98  --bmc1_symbol_reachability              true
% 3.35/0.98  --bmc1_property_lemmas                  false
% 3.35/0.98  --bmc1_k_induction                      false
% 3.35/0.98  --bmc1_non_equiv_states                 false
% 3.35/0.98  --bmc1_deadlock                         false
% 3.35/0.98  --bmc1_ucm                              false
% 3.35/0.98  --bmc1_add_unsat_core                   none
% 3.35/0.98  --bmc1_unsat_core_children              false
% 3.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.35/0.98  --bmc1_out_stat                         full
% 3.35/0.98  --bmc1_ground_init                      false
% 3.35/0.98  --bmc1_pre_inst_next_state              false
% 3.35/0.98  --bmc1_pre_inst_state                   false
% 3.35/0.98  --bmc1_pre_inst_reach_state             false
% 3.35/0.98  --bmc1_out_unsat_core                   false
% 3.35/0.98  --bmc1_aig_witness_out                  false
% 3.35/0.98  --bmc1_verbose                          false
% 3.35/0.98  --bmc1_dump_clauses_tptp                false
% 3.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.35/0.98  --bmc1_dump_file                        -
% 3.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.35/0.98  --bmc1_ucm_extend_mode                  1
% 3.35/0.98  --bmc1_ucm_init_mode                    2
% 3.35/0.98  --bmc1_ucm_cone_mode                    none
% 3.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.35/0.98  --bmc1_ucm_relax_model                  4
% 3.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.35/0.98  --bmc1_ucm_layered_model                none
% 3.35/0.98  --bmc1_ucm_max_lemma_size               10
% 3.35/0.98  
% 3.35/0.98  ------ AIG Options
% 3.35/0.98  
% 3.35/0.98  --aig_mode                              false
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation Options
% 3.35/0.98  
% 3.35/0.98  --instantiation_flag                    true
% 3.35/0.98  --inst_sos_flag                         false
% 3.35/0.98  --inst_sos_phase                        true
% 3.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.35/0.98  --inst_lit_sel_side                     none
% 3.35/0.98  --inst_solver_per_active                1400
% 3.35/0.98  --inst_solver_calls_frac                1.
% 3.35/0.98  --inst_passive_queue_type               priority_queues
% 3.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.35/0.98  --inst_passive_queues_freq              [25;2]
% 3.35/0.98  --inst_dismatching                      true
% 3.35/0.98  --inst_eager_unprocessed_to_passive     true
% 3.35/0.98  --inst_prop_sim_given                   true
% 3.35/0.98  --inst_prop_sim_new                     false
% 3.35/0.98  --inst_subs_new                         false
% 3.35/0.98  --inst_eq_res_simp                      false
% 3.35/0.98  --inst_subs_given                       false
% 3.35/0.98  --inst_orphan_elimination               true
% 3.35/0.98  --inst_learning_loop_flag               true
% 3.35/0.98  --inst_learning_start                   3000
% 3.35/0.98  --inst_learning_factor                  2
% 3.35/0.98  --inst_start_prop_sim_after_learn       3
% 3.35/0.98  --inst_sel_renew                        solver
% 3.35/0.98  --inst_lit_activity_flag                true
% 3.35/0.98  --inst_restr_to_given                   false
% 3.35/0.98  --inst_activity_threshold               500
% 3.35/0.98  --inst_out_proof                        true
% 3.35/0.98  
% 3.35/0.98  ------ Resolution Options
% 3.35/0.98  
% 3.35/0.98  --resolution_flag                       false
% 3.35/0.98  --res_lit_sel                           adaptive
% 3.35/0.98  --res_lit_sel_side                      none
% 3.35/0.98  --res_ordering                          kbo
% 3.35/0.98  --res_to_prop_solver                    active
% 3.35/0.98  --res_prop_simpl_new                    false
% 3.35/0.98  --res_prop_simpl_given                  true
% 3.35/0.98  --res_passive_queue_type                priority_queues
% 3.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.35/0.98  --res_passive_queues_freq               [15;5]
% 3.35/0.98  --res_forward_subs                      full
% 3.35/0.98  --res_backward_subs                     full
% 3.35/0.98  --res_forward_subs_resolution           true
% 3.35/0.98  --res_backward_subs_resolution          true
% 3.35/0.98  --res_orphan_elimination                true
% 3.35/0.98  --res_time_limit                        2.
% 3.35/0.98  --res_out_proof                         true
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Options
% 3.35/0.98  
% 3.35/0.98  --superposition_flag                    true
% 3.35/0.98  --sup_passive_queue_type                priority_queues
% 3.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.35/0.98  --demod_completeness_check              fast
% 3.35/0.98  --demod_use_ground                      true
% 3.35/0.98  --sup_to_prop_solver                    passive
% 3.35/0.98  --sup_prop_simpl_new                    true
% 3.35/0.98  --sup_prop_simpl_given                  true
% 3.35/0.98  --sup_fun_splitting                     false
% 3.35/0.98  --sup_smt_interval                      50000
% 3.35/0.98  
% 3.35/0.98  ------ Superposition Simplification Setup
% 3.35/0.98  
% 3.35/0.98  --sup_indices_passive                   []
% 3.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_full_bw                           [BwDemod]
% 3.35/0.98  --sup_immed_triv                        [TrivRules]
% 3.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_immed_bw_main                     []
% 3.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.35/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.35/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.35/0.98  
% 3.35/0.98  ------ Combination Options
% 3.35/0.98  
% 3.35/0.98  --comb_res_mult                         3
% 3.35/0.98  --comb_sup_mult                         2
% 3.35/0.98  --comb_inst_mult                        10
% 3.35/0.98  
% 3.35/0.98  ------ Debug Options
% 3.35/0.98  
% 3.35/0.98  --dbg_backtrace                         false
% 3.35/0.98  --dbg_dump_prop_clauses                 false
% 3.35/0.98  --dbg_dump_prop_clauses_file            -
% 3.35/0.98  --dbg_out_stat                          false
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  ------ Proving...
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  % SZS status Theorem for theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  fof(f1,axiom,(
% 3.35/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f45,plain,(
% 3.35/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.98    inference(nnf_transformation,[],[f1])).
% 3.35/0.98  
% 3.35/0.98  fof(f46,plain,(
% 3.35/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.98    inference(rectify,[],[f45])).
% 3.35/0.98  
% 3.35/0.98  fof(f47,plain,(
% 3.35/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.35/0.98    introduced(choice_axiom,[])).
% 3.35/0.98  
% 3.35/0.98  fof(f48,plain,(
% 3.35/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.35/0.98  
% 3.35/0.98  fof(f59,plain,(
% 3.35/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f48])).
% 3.35/0.98  
% 3.35/0.98  fof(f3,axiom,(
% 3.35/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f61,plain,(
% 3.35/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f3])).
% 3.35/0.98  
% 3.35/0.98  fof(f9,axiom,(
% 3.35/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f29,plain,(
% 3.35/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.35/0.98    inference(ennf_transformation,[],[f9])).
% 3.35/0.98  
% 3.35/0.98  fof(f72,plain,(
% 3.35/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f29])).
% 3.35/0.98  
% 3.35/0.98  fof(f4,axiom,(
% 3.35/0.98    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f24,plain,(
% 3.35/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.35/0.98    inference(ennf_transformation,[],[f4])).
% 3.35/0.98  
% 3.35/0.98  fof(f62,plain,(
% 3.35/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f24])).
% 3.35/0.98  
% 3.35/0.98  fof(f14,axiom,(
% 3.35/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f78,plain,(
% 3.35/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f14])).
% 3.35/0.98  
% 3.35/0.98  fof(f17,axiom,(
% 3.35/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f83,plain,(
% 3.35/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f17])).
% 3.35/0.98  
% 3.35/0.98  fof(f97,plain,(
% 3.35/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.35/0.98    inference(definition_unfolding,[],[f78,f83])).
% 3.35/0.98  
% 3.35/0.98  fof(f5,axiom,(
% 3.35/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f25,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.35/0.98    inference(ennf_transformation,[],[f5])).
% 3.35/0.98  
% 3.35/0.98  fof(f63,plain,(
% 3.35/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f25])).
% 3.35/0.98  
% 3.35/0.98  fof(f2,axiom,(
% 3.35/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f23,plain,(
% 3.35/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.35/0.98    inference(ennf_transformation,[],[f2])).
% 3.35/0.98  
% 3.35/0.98  fof(f60,plain,(
% 3.35/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f23])).
% 3.35/0.98  
% 3.35/0.98  fof(f8,axiom,(
% 3.35/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f71,plain,(
% 3.35/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f8])).
% 3.35/0.98  
% 3.35/0.98  fof(f95,plain,(
% 3.35/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.35/0.98    inference(definition_unfolding,[],[f71,f83])).
% 3.35/0.98  
% 3.35/0.98  fof(f16,axiom,(
% 3.35/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f37,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.35/0.98    inference(ennf_transformation,[],[f16])).
% 3.35/0.98  
% 3.35/0.98  fof(f38,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.35/0.98    inference(flattening,[],[f37])).
% 3.35/0.98  
% 3.35/0.98  fof(f82,plain,(
% 3.35/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f38])).
% 3.35/0.98  
% 3.35/0.98  fof(f13,axiom,(
% 3.35/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f33,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.35/0.98    inference(ennf_transformation,[],[f13])).
% 3.35/0.98  
% 3.35/0.98  fof(f34,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.98    inference(flattening,[],[f33])).
% 3.35/0.98  
% 3.35/0.98  fof(f53,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.98    inference(nnf_transformation,[],[f34])).
% 3.35/0.98  
% 3.35/0.98  fof(f76,plain,(
% 3.35/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f53])).
% 3.35/0.98  
% 3.35/0.98  fof(f20,conjecture,(
% 3.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f21,negated_conjecture,(
% 3.35/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.35/0.98    inference(negated_conjecture,[],[f20])).
% 3.35/0.98  
% 3.35/0.98  fof(f43,plain,(
% 3.35/0.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.35/0.98    inference(ennf_transformation,[],[f21])).
% 3.35/0.98  
% 3.35/0.98  fof(f44,plain,(
% 3.35/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.35/0.98    inference(flattening,[],[f43])).
% 3.35/0.98  
% 3.35/0.98  fof(f56,plain,(
% 3.35/0.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK6,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK6),k6_partfun1(X0)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK6,X1,X0) & v1_funct_1(sK6))) )),
% 3.35/0.98    introduced(choice_axiom,[])).
% 3.35/0.98  
% 3.35/0.98  fof(f55,plain,(
% 3.35/0.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK3) | ~v2_funct_1(sK5)) & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,X3),k6_partfun1(sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(X3,sK4,sK3) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.35/0.98    introduced(choice_axiom,[])).
% 3.35/0.98  
% 3.35/0.98  fof(f57,plain,(
% 3.35/0.98    ((~v2_funct_2(sK6,sK3) | ~v2_funct_1(sK5)) & r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.35/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f44,f56,f55])).
% 3.35/0.98  
% 3.35/0.98  fof(f93,plain,(
% 3.35/0.98    r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3))),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f87,plain,(
% 3.35/0.98    v1_funct_1(sK5)),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f89,plain,(
% 3.35/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f90,plain,(
% 3.35/0.98    v1_funct_1(sK6)),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f92,plain,(
% 3.35/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f19,axiom,(
% 3.35/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f41,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.35/0.98    inference(ennf_transformation,[],[f19])).
% 3.35/0.98  
% 3.35/0.98  fof(f42,plain,(
% 3.35/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.35/0.98    inference(flattening,[],[f41])).
% 3.35/0.98  
% 3.35/0.98  fof(f85,plain,(
% 3.35/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f42])).
% 3.35/0.98  
% 3.35/0.98  fof(f88,plain,(
% 3.35/0.98    v1_funct_2(sK5,sK3,sK4)),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f91,plain,(
% 3.35/0.98    v1_funct_2(sK6,sK4,sK3)),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  fof(f12,axiom,(
% 3.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f32,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.98    inference(ennf_transformation,[],[f12])).
% 3.35/0.98  
% 3.35/0.98  fof(f75,plain,(
% 3.35/0.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f32])).
% 3.35/0.98  
% 3.35/0.98  fof(f18,axiom,(
% 3.35/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f39,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.35/0.98    inference(ennf_transformation,[],[f18])).
% 3.35/0.98  
% 3.35/0.98  fof(f40,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.35/0.98    inference(flattening,[],[f39])).
% 3.35/0.98  
% 3.35/0.98  fof(f84,plain,(
% 3.35/0.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f40])).
% 3.35/0.98  
% 3.35/0.98  fof(f11,axiom,(
% 3.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f22,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.35/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.35/0.98  
% 3.35/0.98  fof(f31,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.98    inference(ennf_transformation,[],[f22])).
% 3.35/0.98  
% 3.35/0.98  fof(f74,plain,(
% 3.35/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f31])).
% 3.35/0.98  
% 3.35/0.98  fof(f15,axiom,(
% 3.35/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f35,plain,(
% 3.35/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.35/0.98    inference(ennf_transformation,[],[f15])).
% 3.35/0.98  
% 3.35/0.98  fof(f36,plain,(
% 3.35/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.35/0.98    inference(flattening,[],[f35])).
% 3.35/0.98  
% 3.35/0.98  fof(f54,plain,(
% 3.35/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.35/0.98    inference(nnf_transformation,[],[f36])).
% 3.35/0.98  
% 3.35/0.98  fof(f80,plain,(
% 3.35/0.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.35/0.98    inference(cnf_transformation,[],[f54])).
% 3.35/0.98  
% 3.35/0.98  fof(f99,plain,(
% 3.35/0.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.35/0.98    inference(equality_resolution,[],[f80])).
% 3.35/0.98  
% 3.35/0.98  fof(f10,axiom,(
% 3.35/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.35/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.35/0.98  
% 3.35/0.98  fof(f30,plain,(
% 3.35/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.35/0.98    inference(ennf_transformation,[],[f10])).
% 3.35/0.98  
% 3.35/0.98  fof(f73,plain,(
% 3.35/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.35/0.98    inference(cnf_transformation,[],[f30])).
% 3.35/0.98  
% 3.35/0.98  fof(f94,plain,(
% 3.35/0.98    ~v2_funct_2(sK6,sK3) | ~v2_funct_1(sK5)),
% 3.35/0.98    inference(cnf_transformation,[],[f57])).
% 3.35/0.98  
% 3.35/0.98  cnf(c_0,plain,
% 3.35/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1136,plain,
% 3.35/0.98      ( r2_hidden(sK0(X0_55),X0_55) | v1_xboole_0(X0_55) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1759,plain,
% 3.35/0.98      ( r2_hidden(sK0(X0_55),X0_55) = iProver_top
% 3.35/0.98      | v1_xboole_0(X0_55) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3,plain,
% 3.35/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_14,plain,
% 3.35/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_410,plain,
% 3.35/0.98      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.35/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_411,plain,
% 3.35/0.98      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.35/0.98      inference(unflattening,[status(thm)],[c_410]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1110,plain,
% 3.35/0.98      ( ~ r2_hidden(X0_57,k1_xboole_0) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_411]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1785,plain,
% 3.35/0.98      ( r2_hidden(X0_57,k1_xboole_0) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2872,plain,
% 3.35/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1759,c_1785]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4,plain,
% 3.35/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.35/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1133,plain,
% 3.35/0.98      ( ~ v1_xboole_0(X0_55) | v1_xboole_0(k2_zfmisc_1(X0_55,X1_55)) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1762,plain,
% 3.35/0.98      ( v1_xboole_0(X0_55) != iProver_top
% 3.35/0.98      | v1_xboole_0(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_20,plain,
% 3.35/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.35/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1121,plain,
% 3.35/0.98      ( m1_subset_1(k6_partfun1(X0_55),k1_zfmisc_1(k2_zfmisc_1(X0_55,X0_55))) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1774,plain,
% 3.35/0.98      ( m1_subset_1(k6_partfun1(X0_55),k1_zfmisc_1(k2_zfmisc_1(X0_55,X0_55))) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.35/0.98      | ~ r2_hidden(X2,X0)
% 3.35/0.98      | ~ v1_xboole_0(X1) ),
% 3.35/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1132,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 3.35/0.98      | ~ r2_hidden(X0_57,X0_55)
% 3.35/0.98      | ~ v1_xboole_0(X1_55) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1763,plain,
% 3.35/0.98      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 3.35/0.98      | r2_hidden(X0_57,X0_55) != iProver_top
% 3.35/0.98      | v1_xboole_0(X1_55) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2636,plain,
% 3.35/0.98      ( r2_hidden(X0_57,k6_partfun1(X0_55)) != iProver_top
% 3.35/0.98      | v1_xboole_0(k2_zfmisc_1(X0_55,X0_55)) != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1774,c_1763]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5426,plain,
% 3.35/0.98      ( v1_xboole_0(k2_zfmisc_1(X0_55,X0_55)) != iProver_top
% 3.35/0.98      | v1_xboole_0(k6_partfun1(X0_55)) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1759,c_2636]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5478,plain,
% 3.35/0.98      ( v1_xboole_0(X0_55) != iProver_top
% 3.35/0.98      | v1_xboole_0(k6_partfun1(X0_55)) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1762,c_5426]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2,plain,
% 3.35/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.35/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1134,plain,
% 3.35/0.98      ( ~ v1_xboole_0(X0_55) | k1_xboole_0 = X0_55 ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1761,plain,
% 3.35/0.98      ( k1_xboole_0 = X0_55 | v1_xboole_0(X0_55) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5497,plain,
% 3.35/0.98      ( k6_partfun1(X0_55) = k1_xboole_0
% 3.35/0.98      | v1_xboole_0(X0_55) != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_5478,c_1761]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_6489,plain,
% 3.35/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_2872,c_5497]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_12,plain,
% 3.35/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.35/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1125,plain,
% 3.35/0.98      ( v2_funct_1(k6_partfun1(X0_55)) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1770,plain,
% 3.35/0.98      ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_7420,plain,
% 3.35/0.98      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_6489,c_1770]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_23,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.35/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.35/0.98      | ~ v1_funct_1(X0)
% 3.35/0.98      | ~ v1_funct_1(X3) ),
% 3.35/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1120,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 3.35/0.98      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X5_55)))
% 3.35/0.98      | m1_subset_1(k1_partfun1(X4_55,X5_55,X1_55,X2_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 3.35/0.98      | ~ v1_funct_1(X0_55)
% 3.35/0.98      | ~ v1_funct_1(X3_55) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1775,plain,
% 3.35/0.98      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 3.35/0.98      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X5_55))) != iProver_top
% 3.35/0.98      | m1_subset_1(k1_partfun1(X4_55,X5_55,X1_55,X2_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) = iProver_top
% 3.35/0.98      | v1_funct_1(X3_55) != iProver_top
% 3.35/0.98      | v1_funct_1(X0_55) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_19,plain,
% 3.35/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.35/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.98      | X3 = X2 ),
% 3.35/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_29,negated_conjecture,
% 3.35/0.98      ( r2_relset_1(sK3,sK3,k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k6_partfun1(sK3)) ),
% 3.35/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_522,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | X3 = X0
% 3.35/0.98      | k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) != X0
% 3.35/0.98      | k6_partfun1(sK3) != X3
% 3.35/0.98      | sK3 != X2
% 3.35/0.98      | sK3 != X1 ),
% 3.35/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_523,plain,
% 3.35/0.98      ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.35/0.98      | ~ m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.35/0.98      | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
% 3.35/0.98      inference(unflattening,[status(thm)],[c_522]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_66,plain,
% 3.35/0.98      ( m1_subset_1(k6_partfun1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_525,plain,
% 3.35/0.98      ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.35/0.98      | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_523,c_66]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1107,plain,
% 3.35/0.98      ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 3.35/0.98      | k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_525]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1789,plain,
% 3.35/0.98      ( k6_partfun1(sK3) = k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4517,plain,
% 3.35/0.98      ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3)
% 3.35/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.35/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.35/0.98      | v1_funct_1(sK5) != iProver_top
% 3.35/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1775,c_1789]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_35,negated_conjecture,
% 3.35/0.98      ( v1_funct_1(sK5) ),
% 3.35/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_36,plain,
% 3.35/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_33,negated_conjecture,
% 3.35/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.35/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_38,plain,
% 3.35/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_32,negated_conjecture,
% 3.35/0.98      ( v1_funct_1(sK6) ),
% 3.35/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_39,plain,
% 3.35/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_30,negated_conjecture,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.35/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_41,plain,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4606,plain,
% 3.35/0.98      ( k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6) = k6_partfun1(sK3) ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_4517,c_36,c_38,c_39,c_41]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_27,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.98      | ~ v1_funct_2(X3,X4,X1)
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | ~ v1_funct_1(X0)
% 3.35/0.98      | ~ v1_funct_1(X3)
% 3.35/0.98      | v2_funct_1(X3)
% 3.35/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.35/0.98      | k1_xboole_0 = X2 ),
% 3.35/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1117,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 3.35/0.98      | ~ v1_funct_2(X3_55,X4_55,X1_55)
% 3.35/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 3.35/0.98      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55)))
% 3.35/0.98      | ~ v1_funct_1(X0_55)
% 3.35/0.98      | ~ v1_funct_1(X3_55)
% 3.35/0.98      | v2_funct_1(X3_55)
% 3.35/0.98      | ~ v2_funct_1(k1_partfun1(X4_55,X1_55,X1_55,X2_55,X3_55,X0_55))
% 3.35/0.98      | k1_xboole_0 = X2_55 ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_27]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1778,plain,
% 3.35/0.98      ( k1_xboole_0 = X0_55
% 3.35/0.98      | v1_funct_2(X1_55,X2_55,X0_55) != iProver_top
% 3.35/0.98      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 3.35/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X0_55))) != iProver_top
% 3.35/0.98      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 3.35/0.98      | v1_funct_1(X3_55) != iProver_top
% 3.35/0.98      | v1_funct_1(X1_55) != iProver_top
% 3.35/0.98      | v2_funct_1(X3_55) = iProver_top
% 3.35/0.98      | v2_funct_1(k1_partfun1(X4_55,X2_55,X2_55,X0_55,X3_55,X1_55)) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4632,plain,
% 3.35/0.98      ( sK3 = k1_xboole_0
% 3.35/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.35/0.98      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.35/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.35/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.35/0.98      | v1_funct_1(sK5) != iProver_top
% 3.35/0.98      | v1_funct_1(sK6) != iProver_top
% 3.35/0.98      | v2_funct_1(k6_partfun1(sK3)) != iProver_top
% 3.35/0.98      | v2_funct_1(sK5) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_4606,c_1778]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_34,negated_conjecture,
% 3.35/0.98      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.35/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_37,plain,
% 3.35/0.98      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_31,negated_conjecture,
% 3.35/0.98      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.35/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_40,plain,
% 3.35/0.98      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_89,plain,
% 3.35/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_91,plain,
% 3.35/0.98      ( v2_funct_1(k6_partfun1(sK3)) = iProver_top ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_89]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1116,negated_conjecture,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_30]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1779,plain,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_17,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1122,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 3.35/0.98      | k2_relset_1(X1_55,X2_55,X0_55) = k2_relat_1(X0_55) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1773,plain,
% 3.35/0.98      ( k2_relset_1(X0_55,X1_55,X2_55) = k2_relat_1(X2_55)
% 3.35/0.98      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3156,plain,
% 3.35/0.98      ( k2_relset_1(sK4,sK3,sK6) = k2_relat_1(sK6) ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1779,c_1773]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_25,plain,
% 3.35/0.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.35/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.35/0.98      | ~ v1_funct_2(X3,X1,X0)
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.35/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.35/0.98      | ~ v1_funct_1(X3)
% 3.35/0.98      | ~ v1_funct_1(X2)
% 3.35/0.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.35/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_536,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.35/0.98      | ~ v1_funct_2(X3,X2,X1)
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.35/0.98      | ~ v1_funct_1(X3)
% 3.35/0.98      | ~ v1_funct_1(X0)
% 3.35/0.98      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | k2_relset_1(X2,X1,X3) = X1
% 3.35/0.98      | k6_partfun1(X1) != k6_partfun1(sK3)
% 3.35/0.98      | sK3 != X1 ),
% 3.35/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_537,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0,X1,sK3)
% 3.35/0.98      | ~ v1_funct_2(X2,sK3,X1)
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.35/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.35/0.98      | ~ v1_funct_1(X2)
% 3.35/0.98      | ~ v1_funct_1(X0)
% 3.35/0.98      | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | k2_relset_1(X1,sK3,X0) = sK3
% 3.35/0.98      | k6_partfun1(sK3) != k6_partfun1(sK3) ),
% 3.35/0.98      inference(unflattening,[status(thm)],[c_536]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_779,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0,X1,sK3)
% 3.35/0.98      | ~ v1_funct_2(X2,sK3,X1)
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.35/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.35/0.98      | ~ v1_funct_1(X0)
% 3.35/0.98      | ~ v1_funct_1(X2)
% 3.35/0.98      | k1_partfun1(sK3,X1,X1,sK3,X2,X0) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | k2_relset_1(X1,sK3,X0) = sK3 ),
% 3.35/0.98      inference(equality_resolution_simp,[status(thm)],[c_537]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1106,plain,
% 3.35/0.98      ( ~ v1_funct_2(X0_55,X1_55,sK3)
% 3.35/0.98      | ~ v1_funct_2(X2_55,sK3,X1_55)
% 3.35/0.98      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK3)))
% 3.35/0.98      | ~ m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_55)))
% 3.35/0.98      | ~ v1_funct_1(X0_55)
% 3.35/0.98      | ~ v1_funct_1(X2_55)
% 3.35/0.98      | k1_partfun1(sK3,X1_55,X1_55,sK3,X2_55,X0_55) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | k2_relset_1(X1_55,sK3,X0_55) = sK3 ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_779]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1790,plain,
% 3.35/0.98      ( k1_partfun1(sK3,X0_55,X0_55,sK3,X1_55,X2_55) != k1_partfun1(sK3,sK4,sK4,sK3,sK5,sK6)
% 3.35/0.98      | k2_relset_1(X0_55,sK3,X2_55) = sK3
% 3.35/0.98      | v1_funct_2(X2_55,X0_55,sK3) != iProver_top
% 3.35/0.98      | v1_funct_2(X1_55,sK3,X0_55) != iProver_top
% 3.35/0.98      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 3.35/0.98      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_55))) != iProver_top
% 3.35/0.98      | v1_funct_1(X2_55) != iProver_top
% 3.35/0.98      | v1_funct_1(X1_55) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2479,plain,
% 3.35/0.98      ( k2_relset_1(sK4,sK3,sK6) = sK3
% 3.35/0.98      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.35/0.98      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.35/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.35/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.35/0.98      | v1_funct_1(sK5) != iProver_top
% 3.35/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.35/0.98      inference(equality_resolution,[status(thm)],[c_1790]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2482,plain,
% 3.35/0.98      ( k2_relset_1(sK4,sK3,sK6) = sK3 ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_2479,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3164,plain,
% 3.35/0.98      ( k2_relat_1(sK6) = sK3 ),
% 3.35/0.98      inference(light_normalisation,[status(thm)],[c_3156,c_2482]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_16,plain,
% 3.35/0.98      ( v5_relat_1(X0,X1)
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.35/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_21,plain,
% 3.35/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.35/0.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.35/0.98      | ~ v1_relat_1(X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_440,plain,
% 3.35/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.35/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.35/0.98      | ~ v1_relat_1(X0)
% 3.35/0.98      | X0 != X1
% 3.35/0.98      | k2_relat_1(X0) != X3 ),
% 3.35/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_441,plain,
% 3.35/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.35/0.98      | ~ v1_relat_1(X0) ),
% 3.35/0.98      inference(unflattening,[status(thm)],[c_440]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_15,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.35/0.98      | v1_relat_1(X0) ),
% 3.35/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_451,plain,
% 3.35/0.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.35/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.35/0.98      inference(forward_subsumption_resolution,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_441,c_15]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_28,negated_conjecture,
% 3.35/0.98      ( ~ v2_funct_2(sK6,sK3) | ~ v2_funct_1(sK5) ),
% 3.35/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_466,plain,
% 3.35/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.35/0.98      | ~ v2_funct_1(sK5)
% 3.35/0.98      | k2_relat_1(X0) != sK3
% 3.35/0.98      | sK6 != X0 ),
% 3.35/0.98      inference(resolution_lifted,[status(thm)],[c_451,c_28]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_467,plain,
% 3.35/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK6))))
% 3.35/0.98      | ~ v2_funct_1(sK5)
% 3.35/0.98      | k2_relat_1(sK6) != sK3 ),
% 3.35/0.98      inference(unflattening,[status(thm)],[c_466]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1109,plain,
% 3.35/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6))))
% 3.35/0.98      | ~ v2_funct_1(sK5)
% 3.35/0.98      | k2_relat_1(sK6) != sK3 ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_467]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1138,plain,
% 3.35/0.98      ( ~ v2_funct_1(sK5) | sP0_iProver_split | k2_relat_1(sK6) != sK3 ),
% 3.35/0.98      inference(splitting,
% 3.35/0.98                [splitting(split),new_symbols(definition,[])],
% 3.35/0.98                [c_1109]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1786,plain,
% 3.35/0.98      ( k2_relat_1(sK6) != sK3
% 3.35/0.98      | v2_funct_1(sK5) != iProver_top
% 3.35/0.98      | sP0_iProver_split = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3294,plain,
% 3.35/0.98      ( sK3 != sK3
% 3.35/0.98      | v2_funct_1(sK5) != iProver_top
% 3.35/0.98      | sP0_iProver_split = iProver_top ),
% 3.35/0.98      inference(demodulation,[status(thm)],[c_3164,c_1786]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3295,plain,
% 3.35/0.98      ( v2_funct_1(sK5) != iProver_top
% 3.35/0.98      | sP0_iProver_split = iProver_top ),
% 3.35/0.98      inference(equality_resolution_simp,[status(thm)],[c_3294]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1137,plain,
% 3.35/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6))))
% 3.35/0.98      | ~ sP0_iProver_split ),
% 3.35/0.98      inference(splitting,
% 3.35/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.35/0.98                [c_1109]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1787,plain,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK6)))) != iProver_top
% 3.35/0.98      | sP0_iProver_split != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3293,plain,
% 3.35/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK3))) != iProver_top
% 3.35/0.98      | sP0_iProver_split != iProver_top ),
% 3.35/0.98      inference(demodulation,[status(thm)],[c_3164,c_1787]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3619,plain,
% 3.35/0.98      ( sP0_iProver_split != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1779,c_3293]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4715,plain,
% 3.35/0.98      ( sK3 = k1_xboole_0 ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_4632,c_36,c_37,c_38,c_39,c_40,c_41,c_91,c_3295,c_3619]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1113,negated_conjecture,
% 3.35/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.35/0.98      inference(subtyping,[status(esa)],[c_33]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1782,plain,
% 3.35/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2635,plain,
% 3.35/0.98      ( r2_hidden(X0_57,sK5) != iProver_top
% 3.35/0.98      | v1_xboole_0(k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1782,c_1763]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4725,plain,
% 3.35/0.98      ( r2_hidden(X0_57,sK5) != iProver_top
% 3.35/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK4)) != iProver_top ),
% 3.35/0.98      inference(demodulation,[status(thm)],[c_4715,c_2635]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2233,plain,
% 3.35/0.98      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 3.35/0.98      | v1_xboole_0(k1_xboole_0) ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_1136]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2235,plain,
% 3.35/0.98      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.35/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2234,plain,
% 3.35/0.98      ( ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_1110]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2237,plain,
% 3.35/0.98      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_2234]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_1147,plain,
% 3.35/0.98      ( ~ v1_xboole_0(X0_55) | v1_xboole_0(X1_55) | X1_55 != X0_55 ),
% 3.35/0.98      theory(equality) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2660,plain,
% 3.35/0.98      ( v1_xboole_0(X0_55)
% 3.35/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.35/0.98      | X0_55 != k1_xboole_0 ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2665,plain,
% 3.35/0.98      ( X0_55 != k1_xboole_0
% 3.35/0.98      | v1_xboole_0(X0_55) = iProver_top
% 3.35/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.35/0.98      inference(predicate_to_equality,[status(thm)],[c_2660]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_2667,plain,
% 3.35/0.98      ( sK3 != k1_xboole_0
% 3.35/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.35/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.35/0.98      inference(instantiation,[status(thm)],[c_2665]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3288,plain,
% 3.35/0.98      ( r2_hidden(X0_57,sK5) != iProver_top
% 3.35/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1762,c_2635]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4982,plain,
% 3.35/0.98      ( r2_hidden(X0_57,sK5) != iProver_top ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_4725,c_36,c_37,c_38,c_39,c_40,c_41,c_91,c_2235,c_2237,
% 3.35/0.98                 c_2667,c_3288,c_3295,c_3619,c_4632]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_4989,plain,
% 3.35/0.98      ( v1_xboole_0(sK5) = iProver_top ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_1759,c_4982]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5085,plain,
% 3.35/0.98      ( sK5 = k1_xboole_0 ),
% 3.35/0.98      inference(superposition,[status(thm)],[c_4989,c_1761]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_3782,plain,
% 3.35/0.98      ( v2_funct_1(sK5) != iProver_top ),
% 3.35/0.98      inference(global_propositional_subsumption,
% 3.35/0.98                [status(thm)],
% 3.35/0.98                [c_3295,c_3619]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(c_5165,plain,
% 3.35/0.98      ( v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.35/0.98      inference(demodulation,[status(thm)],[c_5085,c_3782]) ).
% 3.35/0.98  
% 3.35/0.98  cnf(contradiction,plain,
% 3.35/0.98      ( $false ),
% 3.35/0.98      inference(minisat,[status(thm)],[c_7420,c_5165]) ).
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.35/0.98  
% 3.35/0.98  ------                               Statistics
% 3.35/0.98  
% 3.35/0.98  ------ General
% 3.35/0.98  
% 3.35/0.98  abstr_ref_over_cycles:                  0
% 3.35/0.98  abstr_ref_under_cycles:                 0
% 3.35/0.98  gc_basic_clause_elim:                   0
% 3.35/0.98  forced_gc_time:                         0
% 3.35/0.98  parsing_time:                           0.011
% 3.35/0.98  unif_index_cands_time:                  0.
% 3.35/0.98  unif_index_add_time:                    0.
% 3.35/0.98  orderings_time:                         0.
% 3.35/0.98  out_proof_time:                         0.014
% 3.35/0.98  total_time:                             0.313
% 3.35/0.98  num_of_symbols:                         63
% 3.35/0.98  num_of_terms:                           13275
% 3.35/0.98  
% 3.35/0.98  ------ Preprocessing
% 3.35/0.98  
% 3.35/0.98  num_of_splits:                          1
% 3.35/0.98  num_of_split_atoms:                     1
% 3.35/0.98  num_of_reused_defs:                     0
% 3.35/0.98  num_eq_ax_congr_red:                    25
% 3.35/0.98  num_of_sem_filtered_clauses:            1
% 3.35/0.98  num_of_subtypes:                        4
% 3.35/0.98  monotx_restored_types:                  1
% 3.35/0.98  sat_num_of_epr_types:                   0
% 3.35/0.98  sat_num_of_non_cyclic_types:            0
% 3.35/0.98  sat_guarded_non_collapsed_types:        2
% 3.35/0.98  num_pure_diseq_elim:                    0
% 3.35/0.98  simp_replaced_by:                       0
% 3.35/0.98  res_preprocessed:                       174
% 3.35/0.98  prep_upred:                             0
% 3.35/0.98  prep_unflattend:                        31
% 3.35/0.98  smt_new_axioms:                         0
% 3.35/0.98  pred_elim_cands:                        7
% 3.35/0.98  pred_elim:                              4
% 3.35/0.98  pred_elim_cl:                           5
% 3.35/0.98  pred_elim_cycles:                       6
% 3.35/0.98  merged_defs:                            0
% 3.35/0.98  merged_defs_ncl:                        0
% 3.35/0.98  bin_hyper_res:                          0
% 3.35/0.98  prep_cycles:                            4
% 3.35/0.98  pred_elim_time:                         0.011
% 3.35/0.98  splitting_time:                         0.
% 3.35/0.98  sem_filter_time:                        0.
% 3.35/0.98  monotx_time:                            0.
% 3.35/0.98  subtype_inf_time:                       0.001
% 3.35/0.98  
% 3.35/0.98  ------ Problem properties
% 3.35/0.98  
% 3.35/0.98  clauses:                                32
% 3.35/0.98  conjectures:                            6
% 3.35/0.98  epr:                                    7
% 3.35/0.98  horn:                                   27
% 3.35/0.98  ground:                                 8
% 3.35/0.98  unary:                                  10
% 3.35/0.98  binary:                                 9
% 3.35/0.98  lits:                                   100
% 3.35/0.98  lits_eq:                                13
% 3.35/0.98  fd_pure:                                0
% 3.35/0.98  fd_pseudo:                              0
% 3.35/0.98  fd_cond:                                2
% 3.35/0.98  fd_pseudo_cond:                         1
% 3.35/0.98  ac_symbols:                             0
% 3.35/0.98  
% 3.35/0.98  ------ Propositional Solver
% 3.35/0.98  
% 3.35/0.98  prop_solver_calls:                      27
% 3.35/0.98  prop_fast_solver_calls:                 1394
% 3.35/0.98  smt_solver_calls:                       0
% 3.35/0.98  smt_fast_solver_calls:                  0
% 3.35/0.98  prop_num_of_clauses:                    3368
% 3.35/0.98  prop_preprocess_simplified:             8434
% 3.35/0.98  prop_fo_subsumed:                       29
% 3.35/0.98  prop_solver_time:                       0.
% 3.35/0.98  smt_solver_time:                        0.
% 3.35/0.98  smt_fast_solver_time:                   0.
% 3.35/0.98  prop_fast_solver_time:                  0.
% 3.35/0.98  prop_unsat_core_time:                   0.
% 3.35/0.98  
% 3.35/0.98  ------ QBF
% 3.35/0.98  
% 3.35/0.98  qbf_q_res:                              0
% 3.35/0.98  qbf_num_tautologies:                    0
% 3.35/0.98  qbf_prep_cycles:                        0
% 3.35/0.98  
% 3.35/0.98  ------ BMC1
% 3.35/0.98  
% 3.35/0.98  bmc1_current_bound:                     -1
% 3.35/0.98  bmc1_last_solved_bound:                 -1
% 3.35/0.98  bmc1_unsat_core_size:                   -1
% 3.35/0.98  bmc1_unsat_core_parents_size:           -1
% 3.35/0.98  bmc1_merge_next_fun:                    0
% 3.35/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.35/0.98  
% 3.35/0.98  ------ Instantiation
% 3.35/0.98  
% 3.35/0.98  inst_num_of_clauses:                    879
% 3.35/0.98  inst_num_in_passive:                    197
% 3.35/0.98  inst_num_in_active:                     481
% 3.35/0.98  inst_num_in_unprocessed:                201
% 3.35/0.98  inst_num_of_loops:                      510
% 3.35/0.98  inst_num_of_learning_restarts:          0
% 3.35/0.98  inst_num_moves_active_passive:          25
% 3.35/0.98  inst_lit_activity:                      0
% 3.35/0.98  inst_lit_activity_moves:                0
% 3.35/0.98  inst_num_tautologies:                   0
% 3.35/0.98  inst_num_prop_implied:                  0
% 3.35/0.98  inst_num_existing_simplified:           0
% 3.35/0.98  inst_num_eq_res_simplified:             0
% 3.35/0.98  inst_num_child_elim:                    0
% 3.35/0.98  inst_num_of_dismatching_blockings:      225
% 3.35/0.98  inst_num_of_non_proper_insts:           431
% 3.35/0.98  inst_num_of_duplicates:                 0
% 3.35/0.98  inst_inst_num_from_inst_to_res:         0
% 3.35/0.98  inst_dismatching_checking_time:         0.
% 3.35/0.98  
% 3.35/0.98  ------ Resolution
% 3.35/0.98  
% 3.35/0.98  res_num_of_clauses:                     0
% 3.35/0.98  res_num_in_passive:                     0
% 3.35/0.98  res_num_in_active:                      0
% 3.35/0.98  res_num_of_loops:                       178
% 3.35/0.98  res_forward_subset_subsumed:            55
% 3.35/0.98  res_backward_subset_subsumed:           0
% 3.35/0.98  res_forward_subsumed:                   0
% 3.35/0.98  res_backward_subsumed:                  0
% 3.35/0.98  res_forward_subsumption_resolution:     4
% 3.35/0.98  res_backward_subsumption_resolution:    0
% 3.35/0.98  res_clause_to_clause_subsumption:       371
% 3.35/0.98  res_orphan_elimination:                 0
% 3.35/0.98  res_tautology_del:                      30
% 3.35/0.98  res_num_eq_res_simplified:              1
% 3.35/0.98  res_num_sel_changes:                    0
% 3.35/0.98  res_moves_from_active_to_pass:          0
% 3.35/0.98  
% 3.35/0.98  ------ Superposition
% 3.35/0.98  
% 3.35/0.98  sup_time_total:                         0.
% 3.35/0.98  sup_time_generating:                    0.
% 3.35/0.98  sup_time_sim_full:                      0.
% 3.35/0.98  sup_time_sim_immed:                     0.
% 3.35/0.98  
% 3.35/0.98  sup_num_of_clauses:                     117
% 3.35/0.98  sup_num_in_active:                      64
% 3.35/0.98  sup_num_in_passive:                     53
% 3.35/0.98  sup_num_of_loops:                       100
% 3.35/0.98  sup_fw_superposition:                   70
% 3.35/0.98  sup_bw_superposition:                   70
% 3.35/0.98  sup_immediate_simplified:               28
% 3.35/0.98  sup_given_eliminated:                   1
% 3.35/0.98  comparisons_done:                       0
% 3.35/0.98  comparisons_avoided:                    0
% 3.35/0.98  
% 3.35/0.98  ------ Simplifications
% 3.35/0.98  
% 3.35/0.98  
% 3.35/0.98  sim_fw_subset_subsumed:                 13
% 3.35/0.98  sim_bw_subset_subsumed:                 2
% 3.35/0.98  sim_fw_subsumed:                        5
% 3.35/0.98  sim_bw_subsumed:                        1
% 3.35/0.98  sim_fw_subsumption_res:                 0
% 3.35/0.98  sim_bw_subsumption_res:                 0
% 3.35/0.98  sim_tautology_del:                      4
% 3.35/0.98  sim_eq_tautology_del:                   6
% 3.35/0.98  sim_eq_res_simp:                        1
% 3.35/0.98  sim_fw_demodulated:                     2
% 3.35/0.98  sim_bw_demodulated:                     37
% 3.35/0.98  sim_light_normalised:                   9
% 3.35/0.98  sim_joinable_taut:                      0
% 3.35/0.98  sim_joinable_simp:                      0
% 3.35/0.98  sim_ac_normalised:                      0
% 3.35/0.98  sim_smt_subsumption:                    0
% 3.35/0.98  
%------------------------------------------------------------------------------
