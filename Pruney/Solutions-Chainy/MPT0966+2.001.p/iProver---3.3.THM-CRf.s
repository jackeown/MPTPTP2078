%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:30 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 663 expanded)
%              Number of clauses        :  123 ( 260 expanded)
%              Number of leaves         :   21 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  578 (3161 expanded)
%              Number of equality atoms :  271 ( 936 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f48,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f48])).

fof(f65,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
        | ~ v1_funct_2(sK6,sK3,sK5)
        | ~ v1_funct_1(sK6) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
      | ~ v1_funct_2(sK6,sK3,sK5)
      | ~ v1_funct_1(sK6) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f49,f65])).

fof(f108,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f39])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f21,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f107,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f110,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f115,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2254,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2257,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4897,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2254,c_2257])).

cnf(c_41,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2255,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5121,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4897,c_2255])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3916,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_2256])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2258,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5387,plain,
    ( k1_relset_1(sK3,X0,sK6) = k1_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3916,c_2258])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_43])).

cnf(c_681,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_683,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_42])).

cnf(c_5385,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2254,c_2258])).

cnf(c_5648,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_683,c_5385])).

cnf(c_40,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_124,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_125,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_139,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_141,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_1376,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2627,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2628,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_2630,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_1375,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2644,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2735,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_1374,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2736,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2823,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2824,plain,
    ( r1_tarski(X0,sK0(X0)) != iProver_top
    | r2_hidden(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_2826,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_2918,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2919,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_229,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_44])).

cnf(c_230,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_29,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_524,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_29,c_27])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_29,c_27])).

cnf(c_529,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_571,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_44])).

cnf(c_572,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_861,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_xboole_0(X0)
    | sK5 != X1
    | sK3 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_572])).

cnf(c_862,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_2240,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_4246,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3916,c_2240])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4381,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4384,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4381])).

cnf(c_5650,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5648,c_40,c_124,c_125,c_141,c_2630,c_2735,c_2736,c_2826,c_2919,c_4246,c_4384,c_5121])).

cnf(c_6462,plain,
    ( k1_relset_1(sK3,X0,sK6) = sK3
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5387,c_5650])).

cnf(c_6469,plain,
    ( k1_relset_1(sK3,sK5,sK6) = sK3 ),
    inference(superposition,[status(thm)],[c_5121,c_6462])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_325,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_392,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_326])).

cnf(c_2253,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_3388,plain,
    ( v1_xboole_0(k2_relset_1(sK3,sK4,sK6)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_2253])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2270,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3645,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3388,c_2270])).

cnf(c_5118,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4897,c_3645])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_130,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_140,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_30,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_728,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | sK3 != X0
    | sK6 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_230])).

cnf(c_729,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | sK6 != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_2247,plain,
    ( sK5 != k1_xboole_0
    | sK6 != k1_xboole_0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2480,plain,
    ( sK5 != k1_xboole_0
    | sK3 = k1_xboole_0
    | sK6 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2247,c_8])).

cnf(c_110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_112,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_129,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_131,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_2815,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
    | sK6 != k1_xboole_0
    | sK3 = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2480,c_112,c_131])).

cnf(c_2816,plain,
    ( sK5 != k1_xboole_0
    | sK3 = k1_xboole_0
    | sK6 != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2815])).

cnf(c_2825,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2929,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2930,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2929])).

cnf(c_3090,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK6)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3092,plain,
    ( ~ v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_1378,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2673,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_3290,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK6),X2)
    | X2 != X1
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_3292,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3290])).

cnf(c_4304,plain,
    ( ~ r1_tarski(sK6,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_4306,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0)
    | v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4304])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4242,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r1_tarski(sK6,k2_zfmisc_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3916,c_2262])).

cnf(c_4582,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_4242])).

cnf(c_4600,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),k1_xboole_0)
    | r1_tarski(sK6,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4582])).

cnf(c_3202,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relat_1(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5003,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_5004,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5003])).

cnf(c_5302,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5118,c_47,c_124,c_125,c_130,c_140,c_141,c_2630,c_2816,c_2825,c_2826,c_2930,c_3092,c_3292,c_4246,c_4306,c_4381,c_4384,c_4600,c_5004,c_5121])).

cnf(c_4335,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_4336,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4335])).

cnf(c_4338,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4336])).

cnf(c_3302,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_2928,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_3301,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_33,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK5 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_230])).

cnf(c_668,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(sK3,sK5,sK6) != sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_669,plain,
    ( k1_relset_1(sK3,sK5,sK6) != sK3
    | k1_xboole_0 = sK5
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6469,c_5302,c_5121,c_5004,c_4384,c_4338,c_3302,c_3301,c_2826,c_669,c_141,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.02  
% 3.00/1.02  ------  iProver source info
% 3.00/1.02  
% 3.00/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.02  git: non_committed_changes: false
% 3.00/1.02  git: last_make_outside_of_git: false
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     num_symb
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       true
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  ------ Parsing...
% 3.00/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.02  ------ Proving...
% 3.00/1.02  ------ Problem Properties 
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  clauses                                 43
% 3.00/1.02  conjectures                             3
% 3.00/1.02  EPR                                     8
% 3.00/1.02  Horn                                    35
% 3.00/1.02  unary                                   5
% 3.00/1.02  binary                                  21
% 3.00/1.02  lits                                    104
% 3.00/1.02  lits eq                                 38
% 3.00/1.02  fd_pure                                 0
% 3.00/1.02  fd_pseudo                               0
% 3.00/1.02  fd_cond                                 2
% 3.00/1.02  fd_pseudo_cond                          1
% 3.00/1.02  AC symbols                              0
% 3.00/1.02  
% 3.00/1.02  ------ Schedule dynamic 5 is on 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  Current options:
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     none
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       false
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ Proving...
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS status Theorem for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  fof(f23,conjecture,(
% 3.00/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f24,negated_conjecture,(
% 3.00/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.00/1.02    inference(negated_conjecture,[],[f23])).
% 3.00/1.02  
% 3.00/1.02  fof(f48,plain,(
% 3.00/1.02    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.00/1.02    inference(ennf_transformation,[],[f24])).
% 3.00/1.02  
% 3.00/1.02  fof(f49,plain,(
% 3.00/1.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.00/1.02    inference(flattening,[],[f48])).
% 3.00/1.02  
% 3.00/1.02  fof(f65,plain,(
% 3.00/1.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f66,plain,(
% 3.00/1.02    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f49,f65])).
% 3.00/1.02  
% 3.00/1.02  fof(f108,plain,(
% 3.00/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f17,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f38,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f17])).
% 3.00/1.02  
% 3.00/1.02  fof(f92,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f38])).
% 3.00/1.02  
% 3.00/1.02  fof(f109,plain,(
% 3.00/1.02    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f18,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f39,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.00/1.02    inference(ennf_transformation,[],[f18])).
% 3.00/1.02  
% 3.00/1.02  fof(f40,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.00/1.02    inference(flattening,[],[f39])).
% 3.00/1.02  
% 3.00/1.02  fof(f93,plain,(
% 3.00/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f40])).
% 3.00/1.02  
% 3.00/1.02  fof(f16,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f37,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f16])).
% 3.00/1.02  
% 3.00/1.02  fof(f91,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f37])).
% 3.00/1.02  
% 3.00/1.02  fof(f21,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f44,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f21])).
% 3.00/1.02  
% 3.00/1.02  fof(f45,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(flattening,[],[f44])).
% 3.00/1.02  
% 3.00/1.02  fof(f64,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(nnf_transformation,[],[f45])).
% 3.00/1.02  
% 3.00/1.02  fof(f97,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f64])).
% 3.00/1.02  
% 3.00/1.02  fof(f107,plain,(
% 3.00/1.02    v1_funct_2(sK6,sK3,sK4)),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f110,plain,(
% 3.00/1.02    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f6,axiom,(
% 3.00/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f58,plain,(
% 3.00/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.02    inference(nnf_transformation,[],[f6])).
% 3.00/1.02  
% 3.00/1.02  fof(f59,plain,(
% 3.00/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.02    inference(flattening,[],[f58])).
% 3.00/1.02  
% 3.00/1.02  fof(f75,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f59])).
% 3.00/1.02  
% 3.00/1.02  fof(f76,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.00/1.02    inference(cnf_transformation,[],[f59])).
% 3.00/1.02  
% 3.00/1.02  fof(f113,plain,(
% 3.00/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.00/1.02    inference(equality_resolution,[],[f76])).
% 3.00/1.02  
% 3.00/1.02  fof(f1,axiom,(
% 3.00/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f50,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(nnf_transformation,[],[f1])).
% 3.00/1.02  
% 3.00/1.02  fof(f51,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(rectify,[],[f50])).
% 3.00/1.02  
% 3.00/1.02  fof(f52,plain,(
% 3.00/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f53,plain,(
% 3.00/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 3.00/1.02  
% 3.00/1.02  fof(f68,plain,(
% 3.00/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f53])).
% 3.00/1.02  
% 3.00/1.02  fof(f13,axiom,(
% 3.00/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f34,plain,(
% 3.00/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.00/1.02    inference(ennf_transformation,[],[f13])).
% 3.00/1.02  
% 3.00/1.02  fof(f88,plain,(
% 3.00/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f34])).
% 3.00/1.02  
% 3.00/1.02  fof(f111,plain,(
% 3.00/1.02    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f106,plain,(
% 3.00/1.02    v1_funct_1(sK6)),
% 3.00/1.02    inference(cnf_transformation,[],[f66])).
% 3.00/1.02  
% 3.00/1.02  fof(f20,axiom,(
% 3.00/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f43,plain,(
% 3.00/1.02    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f20])).
% 3.00/1.02  
% 3.00/1.02  fof(f96,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f43])).
% 3.00/1.02  
% 3.00/1.02  fof(f19,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f41,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(ennf_transformation,[],[f19])).
% 3.00/1.02  
% 3.00/1.02  fof(f42,plain,(
% 3.00/1.02    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.02    inference(flattening,[],[f41])).
% 3.00/1.02  
% 3.00/1.02  fof(f95,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f42])).
% 3.00/1.02  
% 3.00/1.02  fof(f4,axiom,(
% 3.00/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f73,plain,(
% 3.00/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f4])).
% 3.00/1.02  
% 3.00/1.02  fof(f9,axiom,(
% 3.00/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f31,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f9])).
% 3.00/1.02  
% 3.00/1.02  fof(f82,plain,(
% 3.00/1.02    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f31])).
% 3.00/1.02  
% 3.00/1.02  fof(f10,axiom,(
% 3.00/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f62,plain,(
% 3.00/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.00/1.02    inference(nnf_transformation,[],[f10])).
% 3.00/1.02  
% 3.00/1.02  fof(f84,plain,(
% 3.00/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f62])).
% 3.00/1.02  
% 3.00/1.02  fof(f3,axiom,(
% 3.00/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f27,plain,(
% 3.00/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f3])).
% 3.00/1.02  
% 3.00/1.02  fof(f72,plain,(
% 3.00/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f27])).
% 3.00/1.02  
% 3.00/1.02  fof(f102,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f64])).
% 3.00/1.02  
% 3.00/1.02  fof(f114,plain,(
% 3.00/1.02    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(equality_resolution,[],[f102])).
% 3.00/1.02  
% 3.00/1.02  fof(f115,plain,(
% 3.00/1.02    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.00/1.02    inference(equality_resolution,[],[f114])).
% 3.00/1.02  
% 3.00/1.02  fof(f77,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.00/1.02    inference(cnf_transformation,[],[f59])).
% 3.00/1.02  
% 3.00/1.02  fof(f112,plain,(
% 3.00/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.00/1.02    inference(equality_resolution,[],[f77])).
% 3.00/1.02  
% 3.00/1.02  fof(f5,axiom,(
% 3.00/1.02    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.00/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f28,plain,(
% 3.00/1.02    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f5])).
% 3.00/1.02  
% 3.00/1.02  fof(f74,plain,(
% 3.00/1.02    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f28])).
% 3.00/1.02  
% 3.00/1.02  fof(f83,plain,(
% 3.00/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f62])).
% 3.00/1.02  
% 3.00/1.02  fof(f99,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f64])).
% 3.00/1.02  
% 3.00/1.02  cnf(c_42,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2254,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_25,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2257,plain,
% 3.00/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4897,plain,
% 3.00/1.02      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2254,c_2257]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_41,negated_conjecture,
% 3.00/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
% 3.00/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2255,plain,
% 3.00/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5121,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_4897,c_2255]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_26,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.00/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2256,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3916,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2254,c_2256]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_24,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2258,plain,
% 3.00/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5387,plain,
% 3.00/1.02      ( k1_relset_1(sK3,X0,sK6) = k1_relat_1(sK6)
% 3.00/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3916,c_2258]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_35,plain,
% 3.00/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_43,negated_conjecture,
% 3.00/1.02      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.00/1.02      inference(cnf_transformation,[],[f107]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_680,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.00/1.02      | sK4 != X2
% 3.00/1.02      | sK3 != X1
% 3.00/1.02      | sK6 != X0
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_35,c_43]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_681,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.02      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.00/1.02      | k1_xboole_0 = sK4 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_680]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_683,plain,
% 3.00/1.02      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_681,c_42]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5385,plain,
% 3.00/1.02      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2254,c_2258]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5648,plain,
% 3.00/1.02      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_683,c_5385]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_40,negated_conjecture,
% 3.00/1.02      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 3.00/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_10,plain,
% 3.00/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = X0
% 3.00/1.02      | k1_xboole_0 = X1 ),
% 3.00/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_124,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f113]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_125,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_0,plain,
% 3.00/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_139,plain,
% 3.00/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_141,plain,
% 3.00/1.02      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_139]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1376,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.00/1.02      theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2627,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1376]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2628,plain,
% 3.00/1.02      ( sK3 != X0
% 3.00/1.02      | v1_xboole_0(X0) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2630,plain,
% 3.00/1.02      ( sK3 != k1_xboole_0
% 3.00/1.02      | v1_xboole_0(sK3) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2628]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1375,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2644,plain,
% 3.00/1.02      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2735,plain,
% 3.00/1.02      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2644]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1374,plain,( X0 = X0 ),theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2736,plain,
% 3.00/1.02      ( sK3 = sK3 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1374]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_21,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2823,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,sK0(X0)) | ~ r2_hidden(sK0(X0),X0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2824,plain,
% 3.00/1.02      ( r1_tarski(X0,sK0(X0)) != iProver_top
% 3.00/1.02      | r2_hidden(sK0(X0),X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2823]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2826,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) != iProver_top
% 3.00/1.02      | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2824]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2918,plain,
% 3.00/1.02      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2919,plain,
% 3.00/1.02      ( sK4 != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = sK4
% 3.00/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2918]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_39,negated_conjecture,
% 3.00/1.02      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ v1_funct_1(sK6) ),
% 3.00/1.02      inference(cnf_transformation,[],[f111]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_44,negated_conjecture,
% 3.00/1.02      ( v1_funct_1(sK6) ),
% 3.00/1.02      inference(cnf_transformation,[],[f106]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_229,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ v1_funct_2(sK6,sK3,sK5) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_39,c_44]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_230,negated_conjecture,
% 3.00/1.02      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_229]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_29,plain,
% 3.00/1.02      ( v1_partfun1(X0,X1)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ v1_xboole_0(X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_27,plain,
% 3.00/1.02      ( v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ v1_partfun1(X0,X1)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ v1_funct_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_524,plain,
% 3.00/1.02      ( v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_xboole_0(X1) ),
% 3.00/1.02      inference(resolution,[status(thm)],[c_29,c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_528,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_xboole_0(X1) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_524,c_29,c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_529,plain,
% 3.00/1.02      ( v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_xboole_0(X1) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_528]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_571,plain,
% 3.00/1.02      ( v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ v1_xboole_0(X1)
% 3.00/1.02      | sK6 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_529,c_44]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_572,plain,
% 3.00/1.02      ( v1_funct_2(sK6,X0,X1)
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.02      | ~ v1_xboole_0(X0) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_571]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_861,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ v1_xboole_0(X0)
% 3.00/1.02      | sK5 != X1
% 3.00/1.02      | sK3 != X0
% 3.00/1.02      | sK6 != sK6 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_230,c_572]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_862,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ v1_xboole_0(sK3) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_861]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2240,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK3) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4246,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3916,c_2240]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4381,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4384,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_4381]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5650,plain,
% 3.00/1.02      ( k1_relat_1(sK6) = sK3 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_5648,c_40,c_124,c_125,c_141,c_2630,c_2735,c_2736,
% 3.00/1.02                 c_2826,c_2919,c_4246,c_4384,c_5121]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6462,plain,
% 3.00/1.02      ( k1_relset_1(sK3,X0,sK6) = sK3
% 3.00/1.02      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_5387,c_5650]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6469,plain,
% 3.00/1.02      ( k1_relset_1(sK3,sK5,sK6) = sK3 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_5121,c_6462]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_15,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.02      | ~ v1_xboole_0(X1)
% 3.00/1.02      | v1_xboole_0(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_16,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_325,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.00/1.02      inference(prop_impl,[status(thm)],[c_16]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_326,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_325]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_392,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.00/1.02      inference(bin_hyper_res,[status(thm)],[c_15,c_326]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2253,plain,
% 3.00/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.00/1.02      | v1_xboole_0(X1) != iProver_top
% 3.00/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3388,plain,
% 3.00/1.02      ( v1_xboole_0(k2_relset_1(sK3,sK4,sK6)) = iProver_top
% 3.00/1.02      | v1_xboole_0(sK5) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2255,c_2253]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2270,plain,
% 3.00/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3645,plain,
% 3.00/1.02      ( k2_relset_1(sK3,sK4,sK6) = k1_xboole_0
% 3.00/1.02      | v1_xboole_0(sK5) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3388,c_2270]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5118,plain,
% 3.00/1.02      ( k2_relat_1(sK6) = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_4897,c_3645]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_47,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_130,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_140,plain,
% 3.00/1.02      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_30,plain,
% 3.00/1.02      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.00/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.00/1.02      | k1_xboole_0 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f115]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_728,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.00/1.02      | sK5 != k1_xboole_0
% 3.00/1.02      | sK3 != X0
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_230]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_729,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.00/1.02      | sK5 != k1_xboole_0
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = sK3 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_728]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2247,plain,
% 3.00/1.02      ( sK5 != k1_xboole_0
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 = sK3
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.00/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_8,plain,
% 3.00/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f112]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2480,plain,
% 3.00/1.02      ( sK5 != k1_xboole_0
% 3.00/1.02      | sK3 = k1_xboole_0
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.00/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_2247,c_8]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_110,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.00/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_112,plain,
% 3.00/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.00/1.02      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_110]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_129,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_131,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_129]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2815,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | sK3 = k1_xboole_0
% 3.00/1.02      | sK5 != k1_xboole_0 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2480,c_112,c_131]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2816,plain,
% 3.00/1.02      ( sK5 != k1_xboole_0
% 3.00/1.02      | sK3 = k1_xboole_0
% 3.00/1.02      | sK6 != k1_xboole_0
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2815]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2825,plain,
% 3.00/1.02      ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 3.00/1.02      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2823]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2929,plain,
% 3.00/1.02      ( ~ v1_xboole_0(sK5)
% 3.00/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.00/1.02      | sK5 = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2930,plain,
% 3.00/1.02      ( sK5 = k1_xboole_0
% 3.00/1.02      | v1_xboole_0(sK5) != iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2929]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3090,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK6) | sK6 = X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3092,plain,
% 3.00/1.02      ( ~ v1_xboole_0(sK6)
% 3.00/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.00/1.02      | sK6 = k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_3090]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1378,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.00/1.02      theory(equality) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2673,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1)
% 3.00/1.02      | r1_tarski(k2_relat_1(X2),X3)
% 3.00/1.02      | X3 != X1
% 3.00/1.02      | k2_relat_1(X2) != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3290,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1)
% 3.00/1.02      | r1_tarski(k2_relat_1(sK6),X2)
% 3.00/1.02      | X2 != X1
% 3.00/1.02      | k2_relat_1(sK6) != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2673]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3292,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK6),k1_xboole_0)
% 3.00/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.00/1.02      | k2_relat_1(sK6) != k1_xboole_0
% 3.00/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_3290]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4304,plain,
% 3.00/1.02      ( ~ r1_tarski(sK6,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK6) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_392]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4306,plain,
% 3.00/1.02      ( ~ r1_tarski(sK6,k1_xboole_0)
% 3.00/1.02      | v1_xboole_0(sK6)
% 3.00/1.02      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_4304]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_17,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2262,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4242,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 3.00/1.02      | r1_tarski(sK6,k2_zfmisc_1(sK3,X0)) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3916,c_2262]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4582,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.00/1.02      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_8,c_4242]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4600,plain,
% 3.00/1.02      ( ~ r1_tarski(k2_relat_1(sK6),k1_xboole_0)
% 3.00/1.02      | r1_tarski(sK6,k1_xboole_0) ),
% 3.00/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4582]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3202,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(sK6),X0) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_26]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5003,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_3202]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5004,plain,
% 3.00/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) = iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_5003]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5302,plain,
% 3.00/1.02      ( v1_xboole_0(sK5) != iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_5118,c_47,c_124,c_125,c_130,c_140,c_141,c_2630,c_2816,
% 3.00/1.02                 c_2825,c_2826,c_2930,c_3092,c_3292,c_4246,c_4306,c_4381,
% 3.00/1.02                 c_4384,c_4600,c_5004,c_5121]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4335,plain,
% 3.00/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1376]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4336,plain,
% 3.00/1.02      ( sK5 != X0
% 3.00/1.02      | v1_xboole_0(X0) != iProver_top
% 3.00/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_4335]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4338,plain,
% 3.00/1.02      ( sK5 != k1_xboole_0
% 3.00/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.00/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_4336]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3302,plain,
% 3.00/1.02      ( sK5 = sK5 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1374]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2928,plain,
% 3.00/1.02      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1375]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3301,plain,
% 3.00/1.02      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_2928]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_33,plain,
% 3.00/1.02      ( v1_funct_2(X0,X1,X2)
% 3.00/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) != X1
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_667,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | k1_relset_1(X1,X2,X0) != X1
% 3.00/1.02      | sK5 != X2
% 3.00/1.02      | sK3 != X1
% 3.00/1.02      | sK6 != X0
% 3.00/1.02      | k1_xboole_0 = X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_33,c_230]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_668,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.00/1.02      | k1_relset_1(sK3,sK5,sK6) != sK3
% 3.00/1.02      | k1_xboole_0 = sK5 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_667]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_669,plain,
% 3.00/1.02      ( k1_relset_1(sK3,sK5,sK6) != sK3
% 3.00/1.02      | k1_xboole_0 = sK5
% 3.00/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(contradiction,plain,
% 3.00/1.02      ( $false ),
% 3.00/1.02      inference(minisat,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_6469,c_5302,c_5121,c_5004,c_4384,c_4338,c_3302,c_3301,
% 3.00/1.02                 c_2826,c_669,c_141,c_47]) ).
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  ------                               Statistics
% 3.00/1.02  
% 3.00/1.02  ------ General
% 3.00/1.02  
% 3.00/1.02  abstr_ref_over_cycles:                  0
% 3.00/1.02  abstr_ref_under_cycles:                 0
% 3.00/1.02  gc_basic_clause_elim:                   0
% 3.00/1.02  forced_gc_time:                         0
% 3.00/1.02  parsing_time:                           0.01
% 3.00/1.02  unif_index_cands_time:                  0.
% 3.00/1.02  unif_index_add_time:                    0.
% 3.00/1.02  orderings_time:                         0.
% 3.00/1.02  out_proof_time:                         0.012
% 3.00/1.02  total_time:                             0.204
% 3.00/1.02  num_of_symbols:                         54
% 3.00/1.02  num_of_terms:                           4429
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing
% 3.00/1.02  
% 3.00/1.02  num_of_splits:                          0
% 3.00/1.02  num_of_split_atoms:                     0
% 3.00/1.02  num_of_reused_defs:                     0
% 3.00/1.02  num_eq_ax_congr_red:                    22
% 3.00/1.02  num_of_sem_filtered_clauses:            1
% 3.00/1.02  num_of_subtypes:                        0
% 3.00/1.02  monotx_restored_types:                  0
% 3.00/1.02  sat_num_of_epr_types:                   0
% 3.00/1.02  sat_num_of_non_cyclic_types:            0
% 3.00/1.02  sat_guarded_non_collapsed_types:        0
% 3.00/1.02  num_pure_diseq_elim:                    0
% 3.00/1.02  simp_replaced_by:                       0
% 3.00/1.02  res_preprocessed:                       199
% 3.00/1.02  prep_upred:                             0
% 3.00/1.02  prep_unflattend:                        60
% 3.00/1.02  smt_new_axioms:                         0
% 3.00/1.02  pred_elim_cands:                        5
% 3.00/1.02  pred_elim:                              4
% 3.00/1.02  pred_elim_cl:                           0
% 3.00/1.02  pred_elim_cycles:                       7
% 3.00/1.02  merged_defs:                            8
% 3.00/1.02  merged_defs_ncl:                        0
% 3.00/1.02  bin_hyper_res:                          9
% 3.00/1.02  prep_cycles:                            4
% 3.00/1.02  pred_elim_time:                         0.011
% 3.00/1.02  splitting_time:                         0.
% 3.00/1.02  sem_filter_time:                        0.
% 3.00/1.02  monotx_time:                            0.
% 3.00/1.02  subtype_inf_time:                       0.
% 3.00/1.02  
% 3.00/1.02  ------ Problem properties
% 3.00/1.02  
% 3.00/1.02  clauses:                                43
% 3.00/1.02  conjectures:                            3
% 3.00/1.02  epr:                                    8
% 3.00/1.02  horn:                                   35
% 3.00/1.02  ground:                                 16
% 3.00/1.02  unary:                                  5
% 3.00/1.02  binary:                                 21
% 3.00/1.02  lits:                                   104
% 3.00/1.02  lits_eq:                                38
% 3.00/1.02  fd_pure:                                0
% 3.00/1.02  fd_pseudo:                              0
% 3.00/1.02  fd_cond:                                2
% 3.00/1.02  fd_pseudo_cond:                         1
% 3.00/1.02  ac_symbols:                             0
% 3.00/1.02  
% 3.00/1.02  ------ Propositional Solver
% 3.00/1.02  
% 3.00/1.02  prop_solver_calls:                      27
% 3.00/1.02  prop_fast_solver_calls:                 1296
% 3.00/1.02  smt_solver_calls:                       0
% 3.00/1.02  smt_fast_solver_calls:                  0
% 3.00/1.02  prop_num_of_clauses:                    2082
% 3.00/1.02  prop_preprocess_simplified:             7952
% 3.00/1.02  prop_fo_subsumed:                       16
% 3.00/1.02  prop_solver_time:                       0.
% 3.00/1.02  smt_solver_time:                        0.
% 3.00/1.02  smt_fast_solver_time:                   0.
% 3.00/1.02  prop_fast_solver_time:                  0.
% 3.00/1.02  prop_unsat_core_time:                   0.
% 3.00/1.02  
% 3.00/1.02  ------ QBF
% 3.00/1.02  
% 3.00/1.02  qbf_q_res:                              0
% 3.00/1.02  qbf_num_tautologies:                    0
% 3.00/1.02  qbf_prep_cycles:                        0
% 3.00/1.02  
% 3.00/1.02  ------ BMC1
% 3.00/1.02  
% 3.00/1.02  bmc1_current_bound:                     -1
% 3.00/1.02  bmc1_last_solved_bound:                 -1
% 3.00/1.02  bmc1_unsat_core_size:                   -1
% 3.00/1.02  bmc1_unsat_core_parents_size:           -1
% 3.00/1.02  bmc1_merge_next_fun:                    0
% 3.00/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation
% 3.00/1.02  
% 3.00/1.02  inst_num_of_clauses:                    646
% 3.00/1.02  inst_num_in_passive:                    126
% 3.00/1.02  inst_num_in_active:                     340
% 3.00/1.02  inst_num_in_unprocessed:                180
% 3.00/1.02  inst_num_of_loops:                      460
% 3.00/1.02  inst_num_of_learning_restarts:          0
% 3.00/1.02  inst_num_moves_active_passive:          118
% 3.00/1.02  inst_lit_activity:                      0
% 3.00/1.02  inst_lit_activity_moves:                0
% 3.00/1.02  inst_num_tautologies:                   0
% 3.00/1.02  inst_num_prop_implied:                  0
% 3.00/1.02  inst_num_existing_simplified:           0
% 3.00/1.02  inst_num_eq_res_simplified:             0
% 3.00/1.02  inst_num_child_elim:                    0
% 3.00/1.02  inst_num_of_dismatching_blockings:      244
% 3.00/1.02  inst_num_of_non_proper_insts:           654
% 3.00/1.02  inst_num_of_duplicates:                 0
% 3.00/1.02  inst_inst_num_from_inst_to_res:         0
% 3.00/1.02  inst_dismatching_checking_time:         0.
% 3.00/1.02  
% 3.00/1.02  ------ Resolution
% 3.00/1.02  
% 3.00/1.02  res_num_of_clauses:                     0
% 3.00/1.02  res_num_in_passive:                     0
% 3.00/1.02  res_num_in_active:                      0
% 3.00/1.02  res_num_of_loops:                       203
% 3.00/1.02  res_forward_subset_subsumed:            15
% 3.00/1.02  res_backward_subset_subsumed:           0
% 3.00/1.02  res_forward_subsumed:                   0
% 3.00/1.02  res_backward_subsumed:                  0
% 3.00/1.02  res_forward_subsumption_resolution:     3
% 3.00/1.02  res_backward_subsumption_resolution:    0
% 3.00/1.02  res_clause_to_clause_subsumption:       352
% 3.00/1.02  res_orphan_elimination:                 0
% 3.00/1.02  res_tautology_del:                      70
% 3.00/1.02  res_num_eq_res_simplified:              2
% 3.00/1.02  res_num_sel_changes:                    0
% 3.00/1.02  res_moves_from_active_to_pass:          0
% 3.00/1.02  
% 3.00/1.02  ------ Superposition
% 3.00/1.02  
% 3.00/1.02  sup_time_total:                         0.
% 3.00/1.02  sup_time_generating:                    0.
% 3.00/1.02  sup_time_sim_full:                      0.
% 3.00/1.02  sup_time_sim_immed:                     0.
% 3.00/1.02  
% 3.00/1.02  sup_num_of_clauses:                     140
% 3.00/1.02  sup_num_in_active:                      72
% 3.00/1.02  sup_num_in_passive:                     68
% 3.00/1.02  sup_num_of_loops:                       90
% 3.00/1.02  sup_fw_superposition:                   89
% 3.00/1.02  sup_bw_superposition:                   52
% 3.00/1.02  sup_immediate_simplified:               20
% 3.00/1.02  sup_given_eliminated:                   0
% 3.00/1.02  comparisons_done:                       0
% 3.00/1.02  comparisons_avoided:                    4
% 3.00/1.02  
% 3.00/1.02  ------ Simplifications
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  sim_fw_subset_subsumed:                 9
% 3.00/1.02  sim_bw_subset_subsumed:                 1
% 3.00/1.02  sim_fw_subsumed:                        9
% 3.00/1.02  sim_bw_subsumed:                        1
% 3.00/1.02  sim_fw_subsumption_res:                 0
% 3.00/1.02  sim_bw_subsumption_res:                 0
% 3.00/1.02  sim_tautology_del:                      10
% 3.00/1.02  sim_eq_tautology_del:                   2
% 3.00/1.02  sim_eq_res_simp:                        1
% 3.00/1.02  sim_fw_demodulated:                     9
% 3.00/1.02  sim_bw_demodulated:                     18
% 3.00/1.02  sim_light_normalised:                   4
% 3.00/1.02  sim_joinable_taut:                      0
% 3.00/1.02  sim_joinable_simp:                      0
% 3.00/1.02  sim_ac_normalised:                      0
% 3.00/1.02  sim_smt_subsumption:                    0
% 3.00/1.02  
%------------------------------------------------------------------------------
