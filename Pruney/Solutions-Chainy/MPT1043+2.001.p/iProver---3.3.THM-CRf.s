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
% DateTime   : Thu Dec  3 12:08:47 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  245 (5067 expanded)
%              Number of clauses        :  168 (1758 expanded)
%              Number of leaves         :   26 ( 929 expanded)
%              Depth                    :   26
%              Number of atoms          :  662 (18246 expanded)
%              Number of equality atoms :  339 (3126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f62,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ~ r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f62])).

fof(f99,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    ~ r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f36])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

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

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1687,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1669,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1672])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5780,plain,
    ( r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5401,c_37])).

cnf(c_5781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5780])).

cnf(c_5789,plain,
    ( m1_subset_1(sK1(k5_partfun1(sK2,sK3,sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_5781])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6145,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
    | v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_1675])).

cnf(c_34,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_39,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_97,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_32,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_32,c_29])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_457,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_33,c_31])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_1666,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3241,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1666])).

cnf(c_3835,plain,
    ( r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3241,c_37])).

cnf(c_3836,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3835])).

cnf(c_3845,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
    | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),X0),k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_3836])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1688,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4364,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_1688])).

cnf(c_1036,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_12381,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_12387,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12381])).

cnf(c_12389,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12387])).

cnf(c_12425,plain,
    ( v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6145,c_39,c_97,c_4364,c_12389])).

cnf(c_12426,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
    | v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12425])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4618,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1674])).

cnf(c_4949,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(X0,sK4) != iProver_top
    | r2_hidden(X1,k5_partfun1(sK2,sK3,X0)) != iProver_top
    | r2_hidden(X1,k1_funct_2(sK2,sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4618,c_1666])).

cnf(c_6717,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4949,c_39,c_4364])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6388,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1673])).

cnf(c_1910,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
    | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1911,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top
    | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1910])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1980,plain,
    ( ~ r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4))
    | ~ v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1981,plain,
    ( r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) != iProver_top
    | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_6588,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6388,c_37,c_39,c_1911,c_1981])).

cnf(c_6720,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6717,c_6588])).

cnf(c_7474,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6720,c_97])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1684,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7479,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7474,c_1684])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2530,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1678])).

cnf(c_6747,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6717,c_2530])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6756,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6747,c_11])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1681,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1683,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2843,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_1683])).

cnf(c_7643,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6756,c_2843])).

cnf(c_12431,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12426,c_6717,c_7479,c_7643])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1682,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3643,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_1675])).

cnf(c_12222,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_3643])).

cnf(c_12958,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12222,c_1684])).

cnf(c_12972,plain,
    ( k2_zfmisc_1(X0,sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)) = k1_xboole_0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12431,c_12958])).

cnf(c_1670,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6748,plain,
    ( r1_tarski(k5_partfun1(sK2,k1_xboole_0,sK4),k1_funct_2(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6717,c_1670])).

cnf(c_8554,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7479,c_6748])).

cnf(c_10752,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7643,c_8554])).

cnf(c_15778,plain,
    ( k2_zfmisc_1(X0,sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12972,c_10752])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15903,plain,
    ( sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_15778,c_13])).

cnf(c_17577,plain,
    ( sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != X0
    | k1_xboole_0 = X0 ),
    inference(equality_factoring,[status(thm)],[c_15903])).

cnf(c_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_85,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X5 != X3
    | X2 != X4
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2)) != iProver_top
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_1043,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1902,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1903,plain,
    ( X0 != sK4
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_1905,plain,
    ( k1_xboole_0 != sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1914,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1917,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_1919,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_1998,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2002,plain,
    ( k1_xboole_0 = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_1034,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2045,plain,
    ( k1_funct_2(sK2,sK3) = k1_funct_2(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_2006,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2323,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_2324,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1038,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1944,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
    | k5_partfun1(sK2,sK3,sK4) != X0
    | k1_funct_2(sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_2050,plain,
    ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
    | k5_partfun1(sK2,sK3,sK4) != X0
    | k1_funct_2(sK2,sK3) != k1_funct_2(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2415,plain,
    ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4))
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
    | k5_partfun1(sK2,sK3,sK4) != k5_partfun1(X0,X1,X2)
    | k1_funct_2(sK2,sK3) != k1_funct_2(X3,X4) ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_2417,plain,
    ( k5_partfun1(sK2,sK3,sK4) != k5_partfun1(X0,X1,X2)
    | k1_funct_2(sK2,sK3) != k1_funct_2(X3,X4)
    | r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4)) != iProver_top
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_2419,plain,
    ( k5_partfun1(sK2,sK3,sK4) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_funct_2(sK2,sK3) != k1_funct_2(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_1042,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_2416,plain,
    ( k5_partfun1(sK2,sK3,sK4) = k5_partfun1(X0,X1,X2)
    | sK4 != X2
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_2421,plain,
    ( k5_partfun1(sK2,sK3,sK4) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_1035,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2038,plain,
    ( X0 != X1
    | k1_funct_2(sK2,sK3) != X1
    | k1_funct_2(sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_2387,plain,
    ( X0 != k1_funct_2(sK2,sK3)
    | k1_funct_2(sK2,sK3) = X0
    | k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_3191,plain,
    ( k1_funct_2(X0,X1) != k1_funct_2(sK2,sK3)
    | k1_funct_2(sK2,sK3) = k1_funct_2(X0,X1)
    | k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3193,plain,
    ( k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3)
    | k1_funct_2(sK2,sK3) = k1_funct_2(k1_xboole_0,k1_xboole_0)
    | k1_funct_2(k1_xboole_0,k1_xboole_0) != k1_funct_2(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3191])).

cnf(c_1044,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
    theory(equality)).

cnf(c_3192,plain,
    ( X0 != sK3
    | X1 != sK2
    | k1_funct_2(X1,X0) = k1_funct_2(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_3194,plain,
    ( k1_funct_2(k1_xboole_0,k1_xboole_0) = k1_funct_2(sK2,sK3)
    | k1_xboole_0 != sK3
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3192])).

cnf(c_3786,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_3787,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3786])).

cnf(c_2374,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_5208,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_5209,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_5208])).

cnf(c_5325,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5327,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5325])).

cnf(c_3644,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1675])).

cnf(c_6741,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6717,c_3644])).

cnf(c_1689,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2771,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_1689])).

cnf(c_2976,plain,
    ( v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2771,c_1670])).

cnf(c_6744,plain,
    ( v1_xboole_0(k5_partfun1(sK2,k1_xboole_0,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6717,c_2976])).

cnf(c_8553,plain,
    ( v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7479,c_6744])).

cnf(c_10746,plain,
    ( v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7643,c_8553])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1690,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5788,plain,
    ( m1_subset_1(sK0(k5_partfun1(sK2,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_5781])).

cnf(c_6070,plain,
    ( m1_subset_1(sK0(k5_partfun1(sK2,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5788,c_39,c_1911,c_1981])).

cnf(c_6080,plain,
    ( v1_xboole_0(sK0(k5_partfun1(sK2,sK3,sK4))) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6070,c_1675])).

cnf(c_9926,plain,
    ( v1_xboole_0(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6080,c_6717,c_7479])).

cnf(c_1685,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9929,plain,
    ( v1_xboole_0(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9926,c_1685])).

cnf(c_9931,plain,
    ( sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9929,c_1684])).

cnf(c_11423,plain,
    ( sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9931,c_7643])).

cnf(c_11426,plain,
    ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11423,c_1690])).

cnf(c_17559,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15903,c_1688])).

cnf(c_19463,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17577,c_37,c_39,c_84,c_85,c_97,c_481,c_1905,c_1919,c_2002,c_2045,c_2323,c_2324,c_2419,c_2421,c_3193,c_3194,c_3787,c_4364,c_5209,c_5327,c_6720,c_6741,c_7479,c_10746,c_11426,c_17559])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_478,c_33,c_31])).

cnf(c_1665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
    | r2_hidden(X1,k1_funct_2(k1_xboole_0,X2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1665,c_12])).

cnf(c_19502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19463,c_1797])).

cnf(c_19782,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19502])).

cnf(c_81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_83,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_75,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_77,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_59,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19782,c_11426,c_10746,c_6741,c_2002,c_1905,c_97,c_83,c_77,c_61,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.68/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.98  
% 3.68/0.98  ------  iProver source info
% 3.68/0.98  
% 3.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.98  git: non_committed_changes: false
% 3.68/0.98  git: last_make_outside_of_git: false
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    --mode clausify
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         false
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     num_symb
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       true
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     false
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   []
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_full_bw                           [BwDemod]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  ------ Parsing...
% 3.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.98  ------ Proving...
% 3.68/0.98  ------ Problem Properties 
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  clauses                                 30
% 3.68/0.98  conjectures                             3
% 3.68/0.98  EPR                                     9
% 3.68/0.98  Horn                                    25
% 3.68/0.98  unary                                   9
% 3.68/0.98  binary                                  9
% 3.68/0.98  lits                                    71
% 3.68/0.98  lits eq                                 8
% 3.68/0.98  fd_pure                                 0
% 3.68/0.98  fd_pseudo                               0
% 3.68/0.98  fd_cond                                 3
% 3.68/0.98  fd_pseudo_cond                          1
% 3.68/0.98  AC symbols                              0
% 3.68/0.98  
% 3.68/0.98  ------ Schedule dynamic 5 is on 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ 
% 3.68/0.98  Current options:
% 3.68/0.98  ------ 
% 3.68/0.98  
% 3.68/0.98  ------ Input Options
% 3.68/0.98  
% 3.68/0.98  --out_options                           all
% 3.68/0.98  --tptp_safe_out                         true
% 3.68/0.98  --problem_path                          ""
% 3.68/0.98  --include_path                          ""
% 3.68/0.98  --clausifier                            res/vclausify_rel
% 3.68/0.98  --clausifier_options                    --mode clausify
% 3.68/0.98  --stdin                                 false
% 3.68/0.98  --stats_out                             all
% 3.68/0.98  
% 3.68/0.98  ------ General Options
% 3.68/0.98  
% 3.68/0.98  --fof                                   false
% 3.68/0.98  --time_out_real                         305.
% 3.68/0.98  --time_out_virtual                      -1.
% 3.68/0.98  --symbol_type_check                     false
% 3.68/0.98  --clausify_out                          false
% 3.68/0.98  --sig_cnt_out                           false
% 3.68/0.98  --trig_cnt_out                          false
% 3.68/0.98  --trig_cnt_out_tolerance                1.
% 3.68/0.98  --trig_cnt_out_sk_spl                   false
% 3.68/0.98  --abstr_cl_out                          false
% 3.68/0.98  
% 3.68/0.98  ------ Global Options
% 3.68/0.98  
% 3.68/0.98  --schedule                              default
% 3.68/0.98  --add_important_lit                     false
% 3.68/0.98  --prop_solver_per_cl                    1000
% 3.68/0.98  --min_unsat_core                        false
% 3.68/0.98  --soft_assumptions                      false
% 3.68/0.98  --soft_lemma_size                       3
% 3.68/0.98  --prop_impl_unit_size                   0
% 3.68/0.98  --prop_impl_unit                        []
% 3.68/0.98  --share_sel_clauses                     true
% 3.68/0.98  --reset_solvers                         false
% 3.68/0.98  --bc_imp_inh                            [conj_cone]
% 3.68/0.98  --conj_cone_tolerance                   3.
% 3.68/0.98  --extra_neg_conj                        none
% 3.68/0.98  --large_theory_mode                     true
% 3.68/0.98  --prolific_symb_bound                   200
% 3.68/0.98  --lt_threshold                          2000
% 3.68/0.98  --clause_weak_htbl                      true
% 3.68/0.98  --gc_record_bc_elim                     false
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing Options
% 3.68/0.98  
% 3.68/0.98  --preprocessing_flag                    true
% 3.68/0.98  --time_out_prep_mult                    0.1
% 3.68/0.98  --splitting_mode                        input
% 3.68/0.98  --splitting_grd                         true
% 3.68/0.98  --splitting_cvd                         false
% 3.68/0.98  --splitting_cvd_svl                     false
% 3.68/0.98  --splitting_nvd                         32
% 3.68/0.98  --sub_typing                            true
% 3.68/0.98  --prep_gs_sim                           true
% 3.68/0.98  --prep_unflatten                        true
% 3.68/0.98  --prep_res_sim                          true
% 3.68/0.98  --prep_upred                            true
% 3.68/0.98  --prep_sem_filter                       exhaustive
% 3.68/0.98  --prep_sem_filter_out                   false
% 3.68/0.98  --pred_elim                             true
% 3.68/0.98  --res_sim_input                         true
% 3.68/0.98  --eq_ax_congr_red                       true
% 3.68/0.98  --pure_diseq_elim                       true
% 3.68/0.98  --brand_transform                       false
% 3.68/0.98  --non_eq_to_eq                          false
% 3.68/0.98  --prep_def_merge                        true
% 3.68/0.98  --prep_def_merge_prop_impl              false
% 3.68/0.98  --prep_def_merge_mbd                    true
% 3.68/0.98  --prep_def_merge_tr_red                 false
% 3.68/0.98  --prep_def_merge_tr_cl                  false
% 3.68/0.98  --smt_preprocessing                     true
% 3.68/0.98  --smt_ac_axioms                         fast
% 3.68/0.98  --preprocessed_out                      false
% 3.68/0.98  --preprocessed_stats                    false
% 3.68/0.98  
% 3.68/0.98  ------ Abstraction refinement Options
% 3.68/0.98  
% 3.68/0.98  --abstr_ref                             []
% 3.68/0.98  --abstr_ref_prep                        false
% 3.68/0.98  --abstr_ref_until_sat                   false
% 3.68/0.98  --abstr_ref_sig_restrict                funpre
% 3.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.98  --abstr_ref_under                       []
% 3.68/0.98  
% 3.68/0.98  ------ SAT Options
% 3.68/0.98  
% 3.68/0.98  --sat_mode                              false
% 3.68/0.98  --sat_fm_restart_options                ""
% 3.68/0.98  --sat_gr_def                            false
% 3.68/0.98  --sat_epr_types                         true
% 3.68/0.98  --sat_non_cyclic_types                  false
% 3.68/0.98  --sat_finite_models                     false
% 3.68/0.98  --sat_fm_lemmas                         false
% 3.68/0.98  --sat_fm_prep                           false
% 3.68/0.98  --sat_fm_uc_incr                        true
% 3.68/0.98  --sat_out_model                         small
% 3.68/0.98  --sat_out_clauses                       false
% 3.68/0.98  
% 3.68/0.98  ------ QBF Options
% 3.68/0.98  
% 3.68/0.98  --qbf_mode                              false
% 3.68/0.98  --qbf_elim_univ                         false
% 3.68/0.98  --qbf_dom_inst                          none
% 3.68/0.98  --qbf_dom_pre_inst                      false
% 3.68/0.98  --qbf_sk_in                             false
% 3.68/0.98  --qbf_pred_elim                         true
% 3.68/0.98  --qbf_split                             512
% 3.68/0.98  
% 3.68/0.98  ------ BMC1 Options
% 3.68/0.98  
% 3.68/0.98  --bmc1_incremental                      false
% 3.68/0.98  --bmc1_axioms                           reachable_all
% 3.68/0.98  --bmc1_min_bound                        0
% 3.68/0.98  --bmc1_max_bound                        -1
% 3.68/0.98  --bmc1_max_bound_default                -1
% 3.68/0.98  --bmc1_symbol_reachability              true
% 3.68/0.98  --bmc1_property_lemmas                  false
% 3.68/0.98  --bmc1_k_induction                      false
% 3.68/0.98  --bmc1_non_equiv_states                 false
% 3.68/0.98  --bmc1_deadlock                         false
% 3.68/0.98  --bmc1_ucm                              false
% 3.68/0.98  --bmc1_add_unsat_core                   none
% 3.68/0.98  --bmc1_unsat_core_children              false
% 3.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.98  --bmc1_out_stat                         full
% 3.68/0.98  --bmc1_ground_init                      false
% 3.68/0.98  --bmc1_pre_inst_next_state              false
% 3.68/0.98  --bmc1_pre_inst_state                   false
% 3.68/0.98  --bmc1_pre_inst_reach_state             false
% 3.68/0.98  --bmc1_out_unsat_core                   false
% 3.68/0.98  --bmc1_aig_witness_out                  false
% 3.68/0.98  --bmc1_verbose                          false
% 3.68/0.98  --bmc1_dump_clauses_tptp                false
% 3.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.98  --bmc1_dump_file                        -
% 3.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.98  --bmc1_ucm_extend_mode                  1
% 3.68/0.98  --bmc1_ucm_init_mode                    2
% 3.68/0.98  --bmc1_ucm_cone_mode                    none
% 3.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.98  --bmc1_ucm_relax_model                  4
% 3.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.98  --bmc1_ucm_layered_model                none
% 3.68/0.98  --bmc1_ucm_max_lemma_size               10
% 3.68/0.98  
% 3.68/0.98  ------ AIG Options
% 3.68/0.98  
% 3.68/0.98  --aig_mode                              false
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation Options
% 3.68/0.98  
% 3.68/0.98  --instantiation_flag                    true
% 3.68/0.98  --inst_sos_flag                         false
% 3.68/0.98  --inst_sos_phase                        true
% 3.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.98  --inst_lit_sel_side                     none
% 3.68/0.98  --inst_solver_per_active                1400
% 3.68/0.98  --inst_solver_calls_frac                1.
% 3.68/0.98  --inst_passive_queue_type               priority_queues
% 3.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.98  --inst_passive_queues_freq              [25;2]
% 3.68/0.98  --inst_dismatching                      true
% 3.68/0.98  --inst_eager_unprocessed_to_passive     true
% 3.68/0.98  --inst_prop_sim_given                   true
% 3.68/0.98  --inst_prop_sim_new                     false
% 3.68/0.98  --inst_subs_new                         false
% 3.68/0.98  --inst_eq_res_simp                      false
% 3.68/0.98  --inst_subs_given                       false
% 3.68/0.98  --inst_orphan_elimination               true
% 3.68/0.98  --inst_learning_loop_flag               true
% 3.68/0.98  --inst_learning_start                   3000
% 3.68/0.98  --inst_learning_factor                  2
% 3.68/0.98  --inst_start_prop_sim_after_learn       3
% 3.68/0.98  --inst_sel_renew                        solver
% 3.68/0.98  --inst_lit_activity_flag                true
% 3.68/0.98  --inst_restr_to_given                   false
% 3.68/0.98  --inst_activity_threshold               500
% 3.68/0.98  --inst_out_proof                        true
% 3.68/0.98  
% 3.68/0.98  ------ Resolution Options
% 3.68/0.98  
% 3.68/0.98  --resolution_flag                       false
% 3.68/0.98  --res_lit_sel                           adaptive
% 3.68/0.98  --res_lit_sel_side                      none
% 3.68/0.98  --res_ordering                          kbo
% 3.68/0.98  --res_to_prop_solver                    active
% 3.68/0.98  --res_prop_simpl_new                    false
% 3.68/0.98  --res_prop_simpl_given                  true
% 3.68/0.98  --res_passive_queue_type                priority_queues
% 3.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.98  --res_passive_queues_freq               [15;5]
% 3.68/0.98  --res_forward_subs                      full
% 3.68/0.98  --res_backward_subs                     full
% 3.68/0.98  --res_forward_subs_resolution           true
% 3.68/0.98  --res_backward_subs_resolution          true
% 3.68/0.98  --res_orphan_elimination                true
% 3.68/0.98  --res_time_limit                        2.
% 3.68/0.98  --res_out_proof                         true
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Options
% 3.68/0.98  
% 3.68/0.98  --superposition_flag                    true
% 3.68/0.98  --sup_passive_queue_type                priority_queues
% 3.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.98  --demod_completeness_check              fast
% 3.68/0.98  --demod_use_ground                      true
% 3.68/0.98  --sup_to_prop_solver                    passive
% 3.68/0.98  --sup_prop_simpl_new                    true
% 3.68/0.98  --sup_prop_simpl_given                  true
% 3.68/0.98  --sup_fun_splitting                     false
% 3.68/0.98  --sup_smt_interval                      50000
% 3.68/0.98  
% 3.68/0.98  ------ Superposition Simplification Setup
% 3.68/0.98  
% 3.68/0.98  --sup_indices_passive                   []
% 3.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_full_bw                           [BwDemod]
% 3.68/0.98  --sup_immed_triv                        [TrivRules]
% 3.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_immed_bw_main                     []
% 3.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.68/0.98  
% 3.68/0.98  ------ Combination Options
% 3.68/0.98  
% 3.68/0.98  --comb_res_mult                         3
% 3.68/0.98  --comb_sup_mult                         2
% 3.68/0.98  --comb_inst_mult                        10
% 3.68/0.98  
% 3.68/0.98  ------ Debug Options
% 3.68/0.98  
% 3.68/0.98  --dbg_backtrace                         false
% 3.68/0.98  --dbg_dump_prop_clauses                 false
% 3.68/0.98  --dbg_dump_prop_clauses_file            -
% 3.68/0.98  --dbg_out_stat                          false
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  ------ Proving...
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS status Theorem for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  fof(f2,axiom,(
% 3.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f26,plain,(
% 3.68/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f2])).
% 3.68/0.98  
% 3.68/0.98  fof(f52,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(nnf_transformation,[],[f26])).
% 3.68/0.98  
% 3.68/0.98  fof(f53,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(rectify,[],[f52])).
% 3.68/0.98  
% 3.68/0.98  fof(f54,plain,(
% 3.68/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f55,plain,(
% 3.68/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 3.68/0.98  
% 3.68/0.98  fof(f67,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f23,conjecture,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f24,negated_conjecture,(
% 3.68/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.68/0.98    inference(negated_conjecture,[],[f23])).
% 3.68/0.98  
% 3.68/0.98  fof(f46,plain,(
% 3.68/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f24])).
% 3.68/0.98  
% 3.68/0.98  fof(f47,plain,(
% 3.68/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.68/0.98    inference(flattening,[],[f46])).
% 3.68/0.98  
% 3.68/0.98  fof(f62,plain,(
% 3.68/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f63,plain,(
% 3.68/0.98    ~r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f62])).
% 3.68/0.98  
% 3.68/0.98  fof(f99,plain,(
% 3.68/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.68/0.98    inference(cnf_transformation,[],[f63])).
% 3.68/0.98  
% 3.68/0.98  fof(f22,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f44,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f22])).
% 3.68/0.98  
% 3.68/0.98  fof(f45,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.68/0.98    inference(flattening,[],[f44])).
% 3.68/0.98  
% 3.68/0.98  fof(f97,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f45])).
% 3.68/0.98  
% 3.68/0.98  fof(f98,plain,(
% 3.68/0.98    v1_funct_1(sK4)),
% 3.68/0.98    inference(cnf_transformation,[],[f63])).
% 3.68/0.98  
% 3.68/0.98  fof(f17,axiom,(
% 3.68/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f35,plain,(
% 3.68/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f17])).
% 3.68/0.98  
% 3.68/0.98  fof(f89,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f35])).
% 3.68/0.98  
% 3.68/0.98  fof(f100,plain,(
% 3.68/0.98    ~r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))),
% 3.68/0.98    inference(cnf_transformation,[],[f63])).
% 3.68/0.98  
% 3.68/0.98  fof(f3,axiom,(
% 3.68/0.98    v1_xboole_0(k1_xboole_0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f69,plain,(
% 3.68/0.98    v1_xboole_0(k1_xboole_0)),
% 3.68/0.98    inference(cnf_transformation,[],[f3])).
% 3.68/0.98  
% 3.68/0.98  fof(f96,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f45])).
% 3.68/0.98  
% 3.68/0.98  fof(f20,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f40,plain,(
% 3.68/0.98    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.98    inference(ennf_transformation,[],[f20])).
% 3.68/0.98  
% 3.68/0.98  fof(f41,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.98    inference(flattening,[],[f40])).
% 3.68/0.98  
% 3.68/0.98  fof(f92,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f95,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f45])).
% 3.68/0.98  
% 3.68/0.98  fof(f68,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f55])).
% 3.68/0.98  
% 3.68/0.98  fof(f18,axiom,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f36,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.68/0.98    inference(ennf_transformation,[],[f18])).
% 3.68/0.98  
% 3.68/0.98  fof(f37,plain,(
% 3.68/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.68/0.98    inference(flattening,[],[f36])).
% 3.68/0.98  
% 3.68/0.98  fof(f90,plain,(
% 3.68/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f37])).
% 3.68/0.98  
% 3.68/0.98  fof(f19,axiom,(
% 3.68/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f38,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.68/0.98    inference(ennf_transformation,[],[f19])).
% 3.68/0.98  
% 3.68/0.98  fof(f39,plain,(
% 3.68/0.98    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.68/0.98    inference(flattening,[],[f38])).
% 3.68/0.98  
% 3.68/0.98  fof(f91,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f39])).
% 3.68/0.98  
% 3.68/0.98  fof(f1,axiom,(
% 3.68/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f48,plain,(
% 3.68/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.68/0.98    inference(nnf_transformation,[],[f1])).
% 3.68/0.98  
% 3.68/0.98  fof(f49,plain,(
% 3.68/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.68/0.98    inference(rectify,[],[f48])).
% 3.68/0.98  
% 3.68/0.98  fof(f50,plain,(
% 3.68/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.68/0.98    introduced(choice_axiom,[])).
% 3.68/0.98  
% 3.68/0.98  fof(f51,plain,(
% 3.68/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 3.68/0.98  
% 3.68/0.98  fof(f64,plain,(
% 3.68/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f51])).
% 3.68/0.98  
% 3.68/0.98  fof(f4,axiom,(
% 3.68/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f27,plain,(
% 3.68/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.68/0.98    inference(ennf_transformation,[],[f4])).
% 3.68/0.98  
% 3.68/0.98  fof(f70,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f27])).
% 3.68/0.98  
% 3.68/0.98  fof(f9,axiom,(
% 3.68/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f60,plain,(
% 3.68/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.68/0.98    inference(nnf_transformation,[],[f9])).
% 3.68/0.98  
% 3.68/0.98  fof(f79,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f60])).
% 3.68/0.98  
% 3.68/0.98  fof(f7,axiom,(
% 3.68/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f58,plain,(
% 3.68/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.98    inference(nnf_transformation,[],[f7])).
% 3.68/0.98  
% 3.68/0.98  fof(f59,plain,(
% 3.68/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.98    inference(flattening,[],[f58])).
% 3.68/0.98  
% 3.68/0.98  fof(f77,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.68/0.98    inference(cnf_transformation,[],[f59])).
% 3.68/0.98  
% 3.68/0.98  fof(f103,plain,(
% 3.68/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.68/0.98    inference(equality_resolution,[],[f77])).
% 3.68/0.98  
% 3.68/0.98  fof(f6,axiom,(
% 3.68/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f74,plain,(
% 3.68/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f6])).
% 3.68/0.98  
% 3.68/0.98  fof(f5,axiom,(
% 3.68/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f56,plain,(
% 3.68/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.98    inference(nnf_transformation,[],[f5])).
% 3.68/0.98  
% 3.68/0.98  fof(f57,plain,(
% 3.68/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.98    inference(flattening,[],[f56])).
% 3.68/0.98  
% 3.68/0.98  fof(f73,plain,(
% 3.68/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f71,plain,(
% 3.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.68/0.98    inference(cnf_transformation,[],[f57])).
% 3.68/0.98  
% 3.68/0.98  fof(f102,plain,(
% 3.68/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.68/0.98    inference(equality_resolution,[],[f71])).
% 3.68/0.98  
% 3.68/0.98  fof(f80,plain,(
% 3.68/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f60])).
% 3.68/0.98  
% 3.68/0.98  fof(f75,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f59])).
% 3.68/0.98  
% 3.68/0.98  fof(f76,plain,(
% 3.68/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.68/0.98    inference(cnf_transformation,[],[f59])).
% 3.68/0.98  
% 3.68/0.98  fof(f104,plain,(
% 3.68/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.68/0.98    inference(equality_resolution,[],[f76])).
% 3.68/0.98  
% 3.68/0.98  fof(f93,plain,(
% 3.68/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f41])).
% 3.68/0.98  
% 3.68/0.98  fof(f105,plain,(
% 3.68/0.98    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.98    inference(equality_resolution,[],[f93])).
% 3.68/0.98  
% 3.68/0.98  fof(f8,axiom,(
% 3.68/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f78,plain,(
% 3.68/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.68/0.98    inference(cnf_transformation,[],[f8])).
% 3.68/0.98  
% 3.68/0.98  fof(f65,plain,(
% 3.68/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f51])).
% 3.68/0.98  
% 3.68/0.98  fof(f14,axiom,(
% 3.68/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.68/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.98  
% 3.68/0.98  fof(f32,plain,(
% 3.68/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.68/0.98    inference(ennf_transformation,[],[f14])).
% 3.68/0.98  
% 3.68/0.98  fof(f86,plain,(
% 3.68/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.68/0.98    inference(cnf_transformation,[],[f32])).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1687,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.68/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_35,negated_conjecture,
% 3.68/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.68/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1669,plain,
% 3.68/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_31,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | ~ v1_funct_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1672,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.68/0.98      | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5401,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1672]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_36,negated_conjecture,
% 3.68/0.98      ( v1_funct_1(sK4) ),
% 3.68/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_37,plain,
% 3.68/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5780,plain,
% 3.68/0.98      ( r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_5401,c_37]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5781,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_5780]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5789,plain,
% 3.68/0.98      ( m1_subset_1(sK1(k5_partfun1(sK2,sK3,sK4),X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1687,c_5781]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_25,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ v1_xboole_0(X2)
% 3.68/0.98      | v1_xboole_0(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1675,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.98      | v1_xboole_0(X2) != iProver_top
% 3.68/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6145,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_5789,c_1675]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_34,negated_conjecture,
% 3.68/0.98      ( ~ r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_39,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5,plain,
% 3.68/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_97,plain,
% 3.68/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_32,plain,
% 3.68/0.98      ( v1_funct_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 3.68/0.98      | ~ v1_funct_1(X3) ),
% 3.68/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_29,plain,
% 3.68/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_453,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | ~ v1_funct_1(X3)
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(resolution,[status(thm)],[c_32,c_29]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_33,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | v1_funct_1(X3) ),
% 3.68/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_457,plain,
% 3.68/0.98      ( ~ v1_funct_1(X0)
% 3.68/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.68/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_453,c_33,c_31]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_458,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | k1_xboole_0 = X2 ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_457]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1666,plain,
% 3.68/0.98      ( k1_xboole_0 = X0
% 3.68/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.68/0.98      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 3.68/0.98      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 3.68/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3241,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top
% 3.68/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1666]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3835,plain,
% 3.68/0.98      ( r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | sK3 = k1_xboole_0 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_3241,c_37]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3836,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_3835]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3845,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
% 3.68/0.98      | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),X0),k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1687,c_3836]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1688,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.68/0.98      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4364,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_3845,c_1688]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1036,plain,
% 3.68/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12381,plain,
% 3.68/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1036]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12387,plain,
% 3.68/0.98      ( sK3 != X0
% 3.68/0.98      | v1_xboole_0(X0) != iProver_top
% 3.68/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_12381]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12389,plain,
% 3.68/0.98      ( sK3 != k1_xboole_0
% 3.68/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.68/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_12387]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12425,plain,
% 3.68/0.98      ( v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6145,c_39,c_97,c_4364,c_12389]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12426,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),X0) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK1(k5_partfun1(sK2,sK3,sK4),X0)) = iProver_top ),
% 3.68/0.98      inference(renaming,[status(thm)],[c_12425]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_26,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ r1_tarski(X3,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1674,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.68/0.98      | r1_tarski(X3,X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4618,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.68/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1674]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_4949,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0
% 3.68/0.98      | r1_tarski(X0,sK4) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k5_partfun1(sK2,sK3,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_funct_2(sK2,sK3)) = iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_4618,c_1666]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6717,plain,
% 3.68/0.98      ( sK3 = k1_xboole_0 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_4949,c_39,c_4364]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_27,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | ~ v1_xboole_0(X2)
% 3.68/0.98      | v1_xboole_0(X1)
% 3.68/0.98      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1673,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top
% 3.68/0.98      | v1_xboole_0(X2) != iProver_top
% 3.68/0.98      | v1_xboole_0(X1) = iProver_top
% 3.68/0.98      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6388,plain,
% 3.68/0.98      ( v1_funct_1(sK4) != iProver_top
% 3.68/0.98      | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK3) != iProver_top
% 3.68/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1673]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1910,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
% 3.68/0.98      | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1911,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top
% 3.68/0.98      | r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1910]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1,plain,
% 3.68/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1980,plain,
% 3.68/0.98      ( ~ r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4))
% 3.68/0.98      | ~ v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1981,plain,
% 3.68/0.98      ( r2_hidden(sK1(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)),k5_partfun1(sK2,sK3,sK4)) != iProver_top
% 3.68/0.98      | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6588,plain,
% 3.68/0.98      ( v1_xboole_0(sK3) != iProver_top
% 3.68/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6388,c_37,c_39,c_1911,c_1981]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6720,plain,
% 3.68/0.98      ( v1_xboole_0(sK2) = iProver_top
% 3.68/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6717,c_6588]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7474,plain,
% 3.68/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_6720,c_97]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6,plain,
% 3.68/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1684,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7479,plain,
% 3.68/0.98      ( sK2 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_7474,c_1684]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_16,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1678,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2530,plain,
% 3.68/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1678]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6747,plain,
% 3.68/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6717,c_2530]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6756,plain,
% 3.68/0.98      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6747,c_11]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_10,plain,
% 3.68/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1681,plain,
% 3.68/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1683,plain,
% 3.68/0.98      ( X0 = X1
% 3.68/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2843,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1681,c_1683]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_7643,plain,
% 3.68/0.98      ( sK4 = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6756,c_2843]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12431,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X0)) = iProver_top ),
% 3.68/0.98      inference(light_normalisation,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_12426,c_6717,c_7479,c_7643]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9,plain,
% 3.68/0.98      ( r1_tarski(X0,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1682,plain,
% 3.68/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_15,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.68/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1679,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3643,plain,
% 3.68/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.68/0.98      | v1_xboole_0(X2) != iProver_top
% 3.68/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1679,c_1675]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12222,plain,
% 3.68/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.68/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1682,c_3643]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12958,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.68/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_12222,c_1684]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12972,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)) = k1_xboole_0
% 3.68/0.98      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_12431,c_12958]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1670,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6748,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(sK2,k1_xboole_0,sK4),k1_funct_2(sK2,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6717,c_1670]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8554,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_7479,c_6748]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_10752,plain,
% 3.68/0.98      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_7643,c_8554]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_15778,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_12972,c_10752]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_13,plain,
% 3.68/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0
% 3.68/0.98      | k1_xboole_0 = X1 ),
% 3.68/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_15903,plain,
% 3.68/0.98      ( sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_15778,c_13]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_17577,plain,
% 3.68/0.98      ( sK1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != X0
% 3.68/0.98      | k1_xboole_0 = X0 ),
% 3.68/0.98      inference(equality_factoring,[status(thm)],[c_15903]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_84,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_12,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_85,plain,
% 3.68/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_28,plain,
% 3.68/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.68/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 3.68/0.98      | ~ v1_funct_1(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_477,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 3.68/0.98      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 3.68/0.98      | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
% 3.68/0.98      | ~ v1_funct_1(X3)
% 3.68/0.98      | ~ v1_funct_1(X0)
% 3.68/0.98      | X5 != X3
% 3.68/0.98      | X2 != X4
% 3.68/0.98      | k1_xboole_0 != X1 ),
% 3.68/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_478,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.98      | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 3.68/0.98      | ~ v1_funct_1(X2)
% 3.68/0.98      | ~ v1_funct_1(X0) ),
% 3.68/0.98      inference(unflattening,[status(thm)],[c_477]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_479,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.68/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.68/0.98      | r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2)) != iProver_top
% 3.68/0.98      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top
% 3.68/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_481,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.68/0.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_479]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1043,plain,
% 3.68/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1902,plain,
% 3.68/0.98      ( v1_funct_1(X0) | ~ v1_funct_1(sK4) | X0 != sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1043]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1903,plain,
% 3.68/0.98      ( X0 != sK4
% 3.68/0.98      | v1_funct_1(X0) = iProver_top
% 3.68/0.98      | v1_funct_1(sK4) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1902]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1905,plain,
% 3.68/0.98      ( k1_xboole_0 != sK4
% 3.68/0.98      | v1_funct_1(sK4) != iProver_top
% 3.68/0.98      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1903]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_14,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.68/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1914,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1917,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1919,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1917]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1998,plain,
% 3.68/0.98      ( ~ v1_xboole_0(sK4) | k1_xboole_0 = sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2002,plain,
% 3.68/0.98      ( k1_xboole_0 = sK4 | v1_xboole_0(sK4) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1034,plain,( X0 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2045,plain,
% 3.68/0.98      ( k1_funct_2(sK2,sK3) = k1_funct_2(sK2,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1034]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2006,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2323,plain,
% 3.68/0.98      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2006]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2324,plain,
% 3.68/0.98      ( r1_tarski(sK4,sK4) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1038,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1944,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1)
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
% 3.68/0.98      | k5_partfun1(sK2,sK3,sK4) != X0
% 3.68/0.98      | k1_funct_2(sK2,sK3) != X1 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1038]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2050,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
% 3.68/0.98      | k5_partfun1(sK2,sK3,sK4) != X0
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(X1,X2) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1944]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2415,plain,
% 3.68/0.98      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4))
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3))
% 3.68/0.98      | k5_partfun1(sK2,sK3,sK4) != k5_partfun1(X0,X1,X2)
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(X3,X4) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2050]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2417,plain,
% 3.68/0.98      ( k5_partfun1(sK2,sK3,sK4) != k5_partfun1(X0,X1,X2)
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(X3,X4)
% 3.68/0.98      | r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4)) != iProver_top
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2419,plain,
% 3.68/0.98      ( k5_partfun1(sK2,sK3,sK4) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.68/0.98      | r1_tarski(k5_partfun1(sK2,sK3,sK4),k1_funct_2(sK2,sK3)) = iProver_top
% 3.68/0.98      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2417]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1042,plain,
% 3.68/0.98      ( X0 != X1
% 3.68/0.98      | X2 != X3
% 3.68/0.98      | X4 != X5
% 3.68/0.98      | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2416,plain,
% 3.68/0.98      ( k5_partfun1(sK2,sK3,sK4) = k5_partfun1(X0,X1,X2)
% 3.68/0.98      | sK4 != X2
% 3.68/0.98      | sK3 != X1
% 3.68/0.98      | sK2 != X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1042]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2421,plain,
% 3.68/0.98      ( k5_partfun1(sK2,sK3,sK4) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.68/0.98      | sK4 != k1_xboole_0
% 3.68/0.98      | sK3 != k1_xboole_0
% 3.68/0.98      | sK2 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2416]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1035,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2038,plain,
% 3.68/0.98      ( X0 != X1 | k1_funct_2(sK2,sK3) != X1 | k1_funct_2(sK2,sK3) = X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2387,plain,
% 3.68/0.98      ( X0 != k1_funct_2(sK2,sK3)
% 3.68/0.98      | k1_funct_2(sK2,sK3) = X0
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2038]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3191,plain,
% 3.68/0.98      ( k1_funct_2(X0,X1) != k1_funct_2(sK2,sK3)
% 3.68/0.98      | k1_funct_2(sK2,sK3) = k1_funct_2(X0,X1)
% 3.68/0.98      | k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2387]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3193,plain,
% 3.68/0.98      ( k1_funct_2(sK2,sK3) != k1_funct_2(sK2,sK3)
% 3.68/0.98      | k1_funct_2(sK2,sK3) = k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.68/0.98      | k1_funct_2(k1_xboole_0,k1_xboole_0) != k1_funct_2(sK2,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_3191]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1044,plain,
% 3.68/0.98      ( X0 != X1 | X2 != X3 | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
% 3.68/0.98      theory(equality) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3192,plain,
% 3.68/0.98      ( X0 != sK3 | X1 != sK2 | k1_funct_2(X1,X0) = k1_funct_2(sK2,sK3) ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1044]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3194,plain,
% 3.68/0.98      ( k1_funct_2(k1_xboole_0,k1_xboole_0) = k1_funct_2(sK2,sK3)
% 3.68/0.98      | k1_xboole_0 != sK3
% 3.68/0.98      | k1_xboole_0 != sK2 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_3192]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3786,plain,
% 3.68/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3787,plain,
% 3.68/0.98      ( sK3 != k1_xboole_0
% 3.68/0.98      | k1_xboole_0 = sK3
% 3.68/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_3786]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2374,plain,
% 3.68/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5208,plain,
% 3.68/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_2374]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5209,plain,
% 3.68/0.98      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_5208]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5325,plain,
% 3.68/0.98      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5327,plain,
% 3.68/0.98      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_5325]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_3644,plain,
% 3.68/0.98      ( v1_xboole_0(sK4) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1669,c_1675]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6741,plain,
% 3.68/0.98      ( v1_xboole_0(sK4) = iProver_top
% 3.68/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6717,c_3644]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1689,plain,
% 3.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.68/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2771,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1687,c_1689]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_2976,plain,
% 3.68/0.98      ( v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_2771,c_1670]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6744,plain,
% 3.68/0.98      ( v1_xboole_0(k5_partfun1(sK2,k1_xboole_0,sK4)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_6717,c_2976]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_8553,plain,
% 3.68/0.98      ( v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_7479,c_6744]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_10746,plain,
% 3.68/0.98      ( v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_7643,c_8553]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_0,plain,
% 3.68/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1690,plain,
% 3.68/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.68/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_5788,plain,
% 3.68/0.98      ( m1_subset_1(sK0(k5_partfun1(sK2,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top
% 3.68/0.98      | v1_xboole_0(k5_partfun1(sK2,sK3,sK4)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_1690,c_5781]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6070,plain,
% 3.68/0.98      ( m1_subset_1(sK0(k5_partfun1(sK2,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_5788,c_39,c_1911,c_1981]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_6080,plain,
% 3.68/0.98      ( v1_xboole_0(sK0(k5_partfun1(sK2,sK3,sK4))) = iProver_top
% 3.68/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_6070,c_1675]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9926,plain,
% 3.68/0.98      ( v1_xboole_0(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4))) = iProver_top
% 3.68/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_6080,c_6717,c_7479]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1685,plain,
% 3.68/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9929,plain,
% 3.68/0.98      ( v1_xboole_0(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4))) = iProver_top ),
% 3.68/0.98      inference(forward_subsumption_resolution,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_9926,c_1685]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_9931,plain,
% 3.68/0.98      ( sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK4)) = k1_xboole_0 ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_9929,c_1684]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11423,plain,
% 3.68/0.98      ( sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.68/0.98      inference(light_normalisation,[status(thm)],[c_9931,c_7643]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_11426,plain,
% 3.68/0.98      ( r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.68/0.98      | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_11423,c_1690]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_17559,plain,
% 3.68/0.98      ( k1_xboole_0 = X0
% 3.68/0.98      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/0.98      inference(superposition,[status(thm)],[c_15903,c_1688]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19463,plain,
% 3.68/0.98      ( k1_xboole_0 = X0 ),
% 3.68/0.98      inference(global_propositional_subsumption,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_17577,c_37,c_39,c_84,c_85,c_97,c_481,c_1905,c_1919,
% 3.68/0.98                 c_2002,c_2045,c_2323,c_2324,c_2419,c_2421,c_3193,c_3194,
% 3.68/0.98                 c_3787,c_4364,c_5209,c_5327,c_6720,c_6741,c_7479,
% 3.68/0.98                 c_10746,c_11426,c_17559]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_494,plain,
% 3.68/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.68/0.98      | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
% 3.68/0.98      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
% 3.68/0.98      | ~ v1_funct_1(X0) ),
% 3.68/0.98      inference(forward_subsumption_resolution,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_478,c_33,c_31]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1665,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.68/0.98      | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_1797,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_funct_2(k1_xboole_0,X2)) = iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_1665,c_12]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19502,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k5_partfun1(k1_xboole_0,X2,X0)) != iProver_top
% 3.68/0.98      | r2_hidden(X1,k1_xboole_0) = iProver_top
% 3.68/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.98      inference(demodulation,[status(thm)],[c_19463,c_1797]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_19782,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 3.68/0.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_19502]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_81,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_83,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_81]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_75,plain,
% 3.68/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_77,plain,
% 3.68/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_22,plain,
% 3.68/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.68/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_59,plain,
% 3.68/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.68/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.68/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(c_61,plain,
% 3.68/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.68/0.98      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.68/0.98      inference(instantiation,[status(thm)],[c_59]) ).
% 3.68/0.98  
% 3.68/0.98  cnf(contradiction,plain,
% 3.68/0.98      ( $false ),
% 3.68/0.98      inference(minisat,
% 3.68/0.98                [status(thm)],
% 3.68/0.98                [c_19782,c_11426,c_10746,c_6741,c_2002,c_1905,c_97,c_83,
% 3.68/0.98                 c_77,c_61,c_37]) ).
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.98  
% 3.68/0.98  ------                               Statistics
% 3.68/0.98  
% 3.68/0.98  ------ General
% 3.68/0.98  
% 3.68/0.98  abstr_ref_over_cycles:                  0
% 3.68/0.98  abstr_ref_under_cycles:                 0
% 3.68/0.98  gc_basic_clause_elim:                   0
% 3.68/0.98  forced_gc_time:                         0
% 3.68/0.98  parsing_time:                           0.008
% 3.68/0.98  unif_index_cands_time:                  0.
% 3.68/0.98  unif_index_add_time:                    0.
% 3.68/0.98  orderings_time:                         0.
% 3.68/0.98  out_proof_time:                         0.013
% 3.68/0.98  total_time:                             0.456
% 3.68/0.98  num_of_symbols:                         50
% 3.68/0.98  num_of_terms:                           12679
% 3.68/0.98  
% 3.68/0.98  ------ Preprocessing
% 3.68/0.98  
% 3.68/0.98  num_of_splits:                          0
% 3.68/0.98  num_of_split_atoms:                     0
% 3.68/0.98  num_of_reused_defs:                     0
% 3.68/0.98  num_eq_ax_congr_red:                    20
% 3.68/0.98  num_of_sem_filtered_clauses:            4
% 3.68/0.98  num_of_subtypes:                        0
% 3.68/0.98  monotx_restored_types:                  0
% 3.68/0.98  sat_num_of_epr_types:                   0
% 3.68/0.98  sat_num_of_non_cyclic_types:            0
% 3.68/0.98  sat_guarded_non_collapsed_types:        0
% 3.68/0.98  num_pure_diseq_elim:                    0
% 3.68/0.98  simp_replaced_by:                       0
% 3.68/0.98  res_preprocessed:                       182
% 3.68/0.98  prep_upred:                             0
% 3.68/0.98  prep_unflattend:                        6
% 3.68/0.98  smt_new_axioms:                         0
% 3.68/0.98  pred_elim_cands:                        5
% 3.68/0.98  pred_elim:                              2
% 3.68/0.98  pred_elim_cl:                           3
% 3.68/0.98  pred_elim_cycles:                       5
% 3.68/0.98  merged_defs:                            10
% 3.68/0.98  merged_defs_ncl:                        0
% 3.68/0.98  bin_hyper_res:                          11
% 3.68/0.98  prep_cycles:                            5
% 3.68/0.98  pred_elim_time:                         0.004
% 3.68/0.98  splitting_time:                         0.
% 3.68/0.98  sem_filter_time:                        0.
% 3.68/0.98  monotx_time:                            0.
% 3.68/0.98  subtype_inf_time:                       0.
% 3.68/0.98  
% 3.68/0.98  ------ Problem properties
% 3.68/0.98  
% 3.68/0.98  clauses:                                30
% 3.68/0.98  conjectures:                            3
% 3.68/0.98  epr:                                    9
% 3.68/0.98  horn:                                   25
% 3.68/0.98  ground:                                 4
% 3.68/0.98  unary:                                  9
% 3.68/0.98  binary:                                 9
% 3.68/0.98  lits:                                   71
% 3.68/0.98  lits_eq:                                8
% 3.68/0.98  fd_pure:                                0
% 3.68/0.98  fd_pseudo:                              0
% 3.68/0.98  fd_cond:                                3
% 3.68/0.98  fd_pseudo_cond:                         1
% 3.68/0.98  ac_symbols:                             0
% 3.68/0.98  
% 3.68/0.98  ------ Propositional Solver
% 3.68/0.98  
% 3.68/0.98  prop_solver_calls:                      32
% 3.68/0.98  prop_fast_solver_calls:                 1636
% 3.68/0.98  smt_solver_calls:                       0
% 3.68/0.98  smt_fast_solver_calls:                  0
% 3.68/0.98  prop_num_of_clauses:                    6141
% 3.68/0.98  prop_preprocess_simplified:             16663
% 3.68/0.98  prop_fo_subsumed:                       75
% 3.68/0.98  prop_solver_time:                       0.
% 3.68/0.98  smt_solver_time:                        0.
% 3.68/0.98  smt_fast_solver_time:                   0.
% 3.68/0.98  prop_fast_solver_time:                  0.
% 3.68/0.98  prop_unsat_core_time:                   0.
% 3.68/0.98  
% 3.68/0.98  ------ QBF
% 3.68/0.98  
% 3.68/0.98  qbf_q_res:                              0
% 3.68/0.98  qbf_num_tautologies:                    0
% 3.68/0.98  qbf_prep_cycles:                        0
% 3.68/0.98  
% 3.68/0.98  ------ BMC1
% 3.68/0.98  
% 3.68/0.98  bmc1_current_bound:                     -1
% 3.68/0.98  bmc1_last_solved_bound:                 -1
% 3.68/0.98  bmc1_unsat_core_size:                   -1
% 3.68/0.98  bmc1_unsat_core_parents_size:           -1
% 3.68/0.98  bmc1_merge_next_fun:                    0
% 3.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.98  
% 3.68/0.98  ------ Instantiation
% 3.68/0.98  
% 3.68/0.98  inst_num_of_clauses:                    1667
% 3.68/0.98  inst_num_in_passive:                    790
% 3.68/0.98  inst_num_in_active:                     748
% 3.68/0.98  inst_num_in_unprocessed:                129
% 3.68/0.98  inst_num_of_loops:                      930
% 3.68/0.98  inst_num_of_learning_restarts:          0
% 3.68/0.98  inst_num_moves_active_passive:          181
% 3.68/0.98  inst_lit_activity:                      0
% 3.68/0.98  inst_lit_activity_moves:                0
% 3.68/0.98  inst_num_tautologies:                   0
% 3.68/0.98  inst_num_prop_implied:                  0
% 3.68/0.98  inst_num_existing_simplified:           0
% 3.68/0.98  inst_num_eq_res_simplified:             0
% 3.68/0.98  inst_num_child_elim:                    0
% 3.68/0.98  inst_num_of_dismatching_blockings:      1310
% 3.68/0.98  inst_num_of_non_proper_insts:           2043
% 3.68/0.98  inst_num_of_duplicates:                 0
% 3.68/0.98  inst_inst_num_from_inst_to_res:         0
% 3.68/0.98  inst_dismatching_checking_time:         0.
% 3.68/0.98  
% 3.68/0.98  ------ Resolution
% 3.68/0.98  
% 3.68/0.98  res_num_of_clauses:                     0
% 3.68/0.98  res_num_in_passive:                     0
% 3.68/0.98  res_num_in_active:                      0
% 3.68/0.98  res_num_of_loops:                       187
% 3.68/0.98  res_forward_subset_subsumed:            207
% 3.68/0.98  res_backward_subset_subsumed:           4
% 3.68/0.98  res_forward_subsumed:                   0
% 3.68/0.98  res_backward_subsumed:                  0
% 3.68/0.98  res_forward_subsumption_resolution:     4
% 3.68/0.98  res_backward_subsumption_resolution:    0
% 3.68/0.98  res_clause_to_clause_subsumption:       2146
% 3.68/0.98  res_orphan_elimination:                 0
% 3.68/0.98  res_tautology_del:                      152
% 3.68/0.98  res_num_eq_res_simplified:              0
% 3.68/0.98  res_num_sel_changes:                    0
% 3.68/0.98  res_moves_from_active_to_pass:          0
% 3.68/0.98  
% 3.68/0.98  ------ Superposition
% 3.68/0.98  
% 3.68/0.98  sup_time_total:                         0.
% 3.68/0.98  sup_time_generating:                    0.
% 3.68/0.98  sup_time_sim_full:                      0.
% 3.68/0.98  sup_time_sim_immed:                     0.
% 3.68/0.98  
% 3.68/0.98  sup_num_of_clauses:                     296
% 3.68/0.98  sup_num_in_active:                      21
% 3.68/0.98  sup_num_in_passive:                     275
% 3.68/0.98  sup_num_of_loops:                       184
% 3.68/0.98  sup_fw_superposition:                   353
% 3.68/0.98  sup_bw_superposition:                   638
% 3.68/0.98  sup_immediate_simplified:               350
% 3.68/0.98  sup_given_eliminated:                   5
% 3.68/0.98  comparisons_done:                       0
% 3.68/0.98  comparisons_avoided:                    0
% 3.68/0.98  
% 3.68/0.98  ------ Simplifications
% 3.68/0.98  
% 3.68/0.98  
% 3.68/0.98  sim_fw_subset_subsumed:                 270
% 3.68/0.98  sim_bw_subset_subsumed:                 41
% 3.68/0.98  sim_fw_subsumed:                        70
% 3.68/0.98  sim_bw_subsumed:                        1
% 3.68/0.98  sim_fw_subsumption_res:                 3
% 3.68/0.98  sim_bw_subsumption_res:                 0
% 3.68/0.98  sim_tautology_del:                      10
% 3.68/0.98  sim_eq_tautology_del:                   11
% 3.68/0.98  sim_eq_res_simp:                        2
% 3.68/0.98  sim_fw_demodulated:                     48
% 3.68/0.98  sim_bw_demodulated:                     155
% 3.68/0.98  sim_light_normalised:                   78
% 3.68/0.98  sim_joinable_taut:                      0
% 3.68/0.98  sim_joinable_simp:                      0
% 3.68/0.98  sim_ac_normalised:                      0
% 3.68/0.98  sim_smt_subsumption:                    0
% 3.68/0.98  
%------------------------------------------------------------------------------
