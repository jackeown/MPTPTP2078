%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:48 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 925 expanded)
%              Number of clauses        :  103 ( 349 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   22
%              Number of atoms          :  482 (3110 expanded)
%              Number of equality atoms :  213 ( 735 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => r2_hidden(X1,k1_funct_2(X0,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_funct_2(X0,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f40])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1119,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1114,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | r2_hidden(X0,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X4,X4))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X4 != X2
    | X4 != X1
    | X3 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_19])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
    | r2_hidden(X2,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
    | r2_hidden(X2,k1_funct_2(X1,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_349,c_22,c_20])).

cnf(c_1100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(X1,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_2001,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1100])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_57,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_65,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_585,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1298,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_1299,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1301,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_577,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1379,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_1380,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_21,c_18])).

cnf(c_305,plain,
    ( r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_22,c_20])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_1102,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_2805,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1102])).

cnf(c_3273,plain,
    ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2805,c_26])).

cnf(c_3274,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3273])).

cnf(c_3282,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_3274])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1120,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3391,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1120])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3527,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3391,c_28])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1115,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_166])).

cnf(c_219,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_167])).

cnf(c_1103,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_2579,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1103])).

cnf(c_2657,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_2579])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1112,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1504,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1112])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1116,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1891,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1116])).

cnf(c_2776,plain,
    ( k2_zfmisc_1(sK1,sK2) = sK3
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2657,c_1891])).

cnf(c_3530,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
    | v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_2776])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3580,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3530,c_7])).

cnf(c_4949,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2001,c_26,c_56,c_57,c_65,c_1301,c_1380,c_3580])).

cnf(c_4950,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4949])).

cnf(c_4957,plain,
    ( r2_hidden(sK0(k5_partfun1(X0,X0,k1_xboole_0),X1),k1_funct_2(X0,X0)) = iProver_top
    | r1_tarski(k5_partfun1(X0,X0,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_4950])).

cnf(c_7131,plain,
    ( r1_tarski(k5_partfun1(X0,X0,k1_xboole_0),k1_funct_2(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4957,c_1120])).

cnf(c_7156,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7131])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1109])).

cnf(c_4962,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4153,c_65])).

cnf(c_4963,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4962])).

cnf(c_3538,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_1504])).

cnf(c_3547,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3538,c_7])).

cnf(c_1503,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1112])).

cnf(c_1890,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1116])).

cnf(c_3712,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3547,c_1890])).

cnf(c_1106,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2773,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2657,c_1106])).

cnf(c_3533,plain,
    ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3527,c_2773])).

cnf(c_4317,plain,
    ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3712,c_3533])).

cnf(c_4970,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4963,c_4317])).

cnf(c_53,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_55,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_5364,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4970,c_26,c_55,c_56,c_57,c_65,c_1301,c_1380,c_3580])).

cnf(c_2775,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2657,c_1890])).

cnf(c_5374,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5364,c_2775])).

cnf(c_584,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
    theory(equality)).

cnf(c_1713,plain,
    ( k5_partfun1(sK1,sK2,sK3) = k5_partfun1(X0,X1,X2)
    | sK3 != X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_1718,plain,
    ( k5_partfun1(sK1,sK2,sK3) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_578,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1318,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    | k5_partfun1(sK1,sK2,sK3) != X0
    | k1_funct_2(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1397,plain,
    ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    | k5_partfun1(sK1,sK2,sK3) != X0
    | k1_funct_2(sK1,sK2) != k1_funct_2(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_1712,plain,
    ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4))
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    | k5_partfun1(sK1,sK2,sK3) != k5_partfun1(X0,X1,X2)
    | k1_funct_2(sK1,sK2) != k1_funct_2(X3,X4) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1714,plain,
    ( k5_partfun1(sK1,sK2,sK3) != k5_partfun1(X0,X1,X2)
    | k1_funct_2(sK1,sK2) != k1_funct_2(X3,X4)
    | r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4)) != iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_1716,plain,
    ( k5_partfun1(sK1,sK2,sK3) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_funct_2(sK1,sK2) != k1_funct_2(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_586,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
    theory(equality)).

cnf(c_1398,plain,
    ( k1_funct_2(sK1,sK2) = k1_funct_2(X0,X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_1403,plain,
    ( k1_funct_2(sK1,sK2) = k1_funct_2(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7156,c_5374,c_3580,c_3391,c_1718,c_1716,c_1403,c_65,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.21/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/1.00  
% 3.21/1.00  ------  iProver source info
% 3.21/1.00  
% 3.21/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.21/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/1.00  git: non_committed_changes: false
% 3.21/1.00  git: last_make_outside_of_git: false
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     num_symb
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       true
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  ------ Parsing...
% 3.21/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.00  ------ Proving...
% 3.21/1.00  ------ Problem Properties 
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  clauses                                 24
% 3.21/1.00  conjectures                             3
% 3.21/1.00  EPR                                     6
% 3.21/1.00  Horn                                    20
% 3.21/1.00  unary                                   8
% 3.21/1.00  binary                                  4
% 3.21/1.00  lits                                    60
% 3.21/1.00  lits eq                                 7
% 3.21/1.00  fd_pure                                 0
% 3.21/1.00  fd_pseudo                               0
% 3.21/1.00  fd_cond                                 2
% 3.21/1.00  fd_pseudo_cond                          1
% 3.21/1.00  AC symbols                              0
% 3.21/1.00  
% 3.21/1.00  ------ Schedule dynamic 5 is on 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ 
% 3.21/1.00  Current options:
% 3.21/1.00  ------ 
% 3.21/1.00  
% 3.21/1.00  ------ Input Options
% 3.21/1.00  
% 3.21/1.00  --out_options                           all
% 3.21/1.00  --tptp_safe_out                         true
% 3.21/1.00  --problem_path                          ""
% 3.21/1.00  --include_path                          ""
% 3.21/1.00  --clausifier                            res/vclausify_rel
% 3.21/1.00  --clausifier_options                    --mode clausify
% 3.21/1.00  --stdin                                 false
% 3.21/1.00  --stats_out                             all
% 3.21/1.00  
% 3.21/1.00  ------ General Options
% 3.21/1.00  
% 3.21/1.00  --fof                                   false
% 3.21/1.00  --time_out_real                         305.
% 3.21/1.00  --time_out_virtual                      -1.
% 3.21/1.00  --symbol_type_check                     false
% 3.21/1.00  --clausify_out                          false
% 3.21/1.00  --sig_cnt_out                           false
% 3.21/1.00  --trig_cnt_out                          false
% 3.21/1.00  --trig_cnt_out_tolerance                1.
% 3.21/1.00  --trig_cnt_out_sk_spl                   false
% 3.21/1.00  --abstr_cl_out                          false
% 3.21/1.00  
% 3.21/1.00  ------ Global Options
% 3.21/1.00  
% 3.21/1.00  --schedule                              default
% 3.21/1.00  --add_important_lit                     false
% 3.21/1.00  --prop_solver_per_cl                    1000
% 3.21/1.00  --min_unsat_core                        false
% 3.21/1.00  --soft_assumptions                      false
% 3.21/1.00  --soft_lemma_size                       3
% 3.21/1.00  --prop_impl_unit_size                   0
% 3.21/1.00  --prop_impl_unit                        []
% 3.21/1.00  --share_sel_clauses                     true
% 3.21/1.00  --reset_solvers                         false
% 3.21/1.00  --bc_imp_inh                            [conj_cone]
% 3.21/1.00  --conj_cone_tolerance                   3.
% 3.21/1.00  --extra_neg_conj                        none
% 3.21/1.00  --large_theory_mode                     true
% 3.21/1.00  --prolific_symb_bound                   200
% 3.21/1.00  --lt_threshold                          2000
% 3.21/1.00  --clause_weak_htbl                      true
% 3.21/1.00  --gc_record_bc_elim                     false
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing Options
% 3.21/1.00  
% 3.21/1.00  --preprocessing_flag                    true
% 3.21/1.00  --time_out_prep_mult                    0.1
% 3.21/1.00  --splitting_mode                        input
% 3.21/1.00  --splitting_grd                         true
% 3.21/1.00  --splitting_cvd                         false
% 3.21/1.00  --splitting_cvd_svl                     false
% 3.21/1.00  --splitting_nvd                         32
% 3.21/1.00  --sub_typing                            true
% 3.21/1.00  --prep_gs_sim                           true
% 3.21/1.00  --prep_unflatten                        true
% 3.21/1.00  --prep_res_sim                          true
% 3.21/1.00  --prep_upred                            true
% 3.21/1.00  --prep_sem_filter                       exhaustive
% 3.21/1.00  --prep_sem_filter_out                   false
% 3.21/1.00  --pred_elim                             true
% 3.21/1.00  --res_sim_input                         true
% 3.21/1.00  --eq_ax_congr_red                       true
% 3.21/1.00  --pure_diseq_elim                       true
% 3.21/1.00  --brand_transform                       false
% 3.21/1.00  --non_eq_to_eq                          false
% 3.21/1.00  --prep_def_merge                        true
% 3.21/1.00  --prep_def_merge_prop_impl              false
% 3.21/1.00  --prep_def_merge_mbd                    true
% 3.21/1.00  --prep_def_merge_tr_red                 false
% 3.21/1.00  --prep_def_merge_tr_cl                  false
% 3.21/1.00  --smt_preprocessing                     true
% 3.21/1.00  --smt_ac_axioms                         fast
% 3.21/1.00  --preprocessed_out                      false
% 3.21/1.00  --preprocessed_stats                    false
% 3.21/1.00  
% 3.21/1.00  ------ Abstraction refinement Options
% 3.21/1.00  
% 3.21/1.00  --abstr_ref                             []
% 3.21/1.00  --abstr_ref_prep                        false
% 3.21/1.00  --abstr_ref_until_sat                   false
% 3.21/1.00  --abstr_ref_sig_restrict                funpre
% 3.21/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.00  --abstr_ref_under                       []
% 3.21/1.00  
% 3.21/1.00  ------ SAT Options
% 3.21/1.00  
% 3.21/1.00  --sat_mode                              false
% 3.21/1.00  --sat_fm_restart_options                ""
% 3.21/1.00  --sat_gr_def                            false
% 3.21/1.00  --sat_epr_types                         true
% 3.21/1.00  --sat_non_cyclic_types                  false
% 3.21/1.00  --sat_finite_models                     false
% 3.21/1.00  --sat_fm_lemmas                         false
% 3.21/1.00  --sat_fm_prep                           false
% 3.21/1.00  --sat_fm_uc_incr                        true
% 3.21/1.00  --sat_out_model                         small
% 3.21/1.00  --sat_out_clauses                       false
% 3.21/1.00  
% 3.21/1.00  ------ QBF Options
% 3.21/1.00  
% 3.21/1.00  --qbf_mode                              false
% 3.21/1.00  --qbf_elim_univ                         false
% 3.21/1.00  --qbf_dom_inst                          none
% 3.21/1.00  --qbf_dom_pre_inst                      false
% 3.21/1.00  --qbf_sk_in                             false
% 3.21/1.00  --qbf_pred_elim                         true
% 3.21/1.00  --qbf_split                             512
% 3.21/1.00  
% 3.21/1.00  ------ BMC1 Options
% 3.21/1.00  
% 3.21/1.00  --bmc1_incremental                      false
% 3.21/1.00  --bmc1_axioms                           reachable_all
% 3.21/1.00  --bmc1_min_bound                        0
% 3.21/1.00  --bmc1_max_bound                        -1
% 3.21/1.00  --bmc1_max_bound_default                -1
% 3.21/1.00  --bmc1_symbol_reachability              true
% 3.21/1.00  --bmc1_property_lemmas                  false
% 3.21/1.00  --bmc1_k_induction                      false
% 3.21/1.00  --bmc1_non_equiv_states                 false
% 3.21/1.00  --bmc1_deadlock                         false
% 3.21/1.00  --bmc1_ucm                              false
% 3.21/1.00  --bmc1_add_unsat_core                   none
% 3.21/1.00  --bmc1_unsat_core_children              false
% 3.21/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.00  --bmc1_out_stat                         full
% 3.21/1.00  --bmc1_ground_init                      false
% 3.21/1.00  --bmc1_pre_inst_next_state              false
% 3.21/1.00  --bmc1_pre_inst_state                   false
% 3.21/1.00  --bmc1_pre_inst_reach_state             false
% 3.21/1.00  --bmc1_out_unsat_core                   false
% 3.21/1.00  --bmc1_aig_witness_out                  false
% 3.21/1.00  --bmc1_verbose                          false
% 3.21/1.00  --bmc1_dump_clauses_tptp                false
% 3.21/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.00  --bmc1_dump_file                        -
% 3.21/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.00  --bmc1_ucm_extend_mode                  1
% 3.21/1.00  --bmc1_ucm_init_mode                    2
% 3.21/1.00  --bmc1_ucm_cone_mode                    none
% 3.21/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.00  --bmc1_ucm_relax_model                  4
% 3.21/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.00  --bmc1_ucm_layered_model                none
% 3.21/1.00  --bmc1_ucm_max_lemma_size               10
% 3.21/1.00  
% 3.21/1.00  ------ AIG Options
% 3.21/1.00  
% 3.21/1.00  --aig_mode                              false
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation Options
% 3.21/1.00  
% 3.21/1.00  --instantiation_flag                    true
% 3.21/1.00  --inst_sos_flag                         false
% 3.21/1.00  --inst_sos_phase                        true
% 3.21/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.00  --inst_lit_sel_side                     none
% 3.21/1.00  --inst_solver_per_active                1400
% 3.21/1.00  --inst_solver_calls_frac                1.
% 3.21/1.00  --inst_passive_queue_type               priority_queues
% 3.21/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.00  --inst_passive_queues_freq              [25;2]
% 3.21/1.00  --inst_dismatching                      true
% 3.21/1.00  --inst_eager_unprocessed_to_passive     true
% 3.21/1.00  --inst_prop_sim_given                   true
% 3.21/1.00  --inst_prop_sim_new                     false
% 3.21/1.00  --inst_subs_new                         false
% 3.21/1.00  --inst_eq_res_simp                      false
% 3.21/1.00  --inst_subs_given                       false
% 3.21/1.00  --inst_orphan_elimination               true
% 3.21/1.00  --inst_learning_loop_flag               true
% 3.21/1.00  --inst_learning_start                   3000
% 3.21/1.00  --inst_learning_factor                  2
% 3.21/1.00  --inst_start_prop_sim_after_learn       3
% 3.21/1.00  --inst_sel_renew                        solver
% 3.21/1.00  --inst_lit_activity_flag                true
% 3.21/1.00  --inst_restr_to_given                   false
% 3.21/1.00  --inst_activity_threshold               500
% 3.21/1.00  --inst_out_proof                        true
% 3.21/1.00  
% 3.21/1.00  ------ Resolution Options
% 3.21/1.00  
% 3.21/1.00  --resolution_flag                       false
% 3.21/1.00  --res_lit_sel                           adaptive
% 3.21/1.00  --res_lit_sel_side                      none
% 3.21/1.00  --res_ordering                          kbo
% 3.21/1.00  --res_to_prop_solver                    active
% 3.21/1.00  --res_prop_simpl_new                    false
% 3.21/1.00  --res_prop_simpl_given                  true
% 3.21/1.00  --res_passive_queue_type                priority_queues
% 3.21/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.00  --res_passive_queues_freq               [15;5]
% 3.21/1.00  --res_forward_subs                      full
% 3.21/1.00  --res_backward_subs                     full
% 3.21/1.00  --res_forward_subs_resolution           true
% 3.21/1.00  --res_backward_subs_resolution          true
% 3.21/1.00  --res_orphan_elimination                true
% 3.21/1.00  --res_time_limit                        2.
% 3.21/1.00  --res_out_proof                         true
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Options
% 3.21/1.00  
% 3.21/1.00  --superposition_flag                    true
% 3.21/1.00  --sup_passive_queue_type                priority_queues
% 3.21/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.00  --demod_completeness_check              fast
% 3.21/1.00  --demod_use_ground                      true
% 3.21/1.00  --sup_to_prop_solver                    passive
% 3.21/1.00  --sup_prop_simpl_new                    true
% 3.21/1.00  --sup_prop_simpl_given                  true
% 3.21/1.00  --sup_fun_splitting                     false
% 3.21/1.00  --sup_smt_interval                      50000
% 3.21/1.00  
% 3.21/1.00  ------ Superposition Simplification Setup
% 3.21/1.00  
% 3.21/1.00  --sup_indices_passive                   []
% 3.21/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_full_bw                           [BwDemod]
% 3.21/1.00  --sup_immed_triv                        [TrivRules]
% 3.21/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_immed_bw_main                     []
% 3.21/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.00  
% 3.21/1.00  ------ Combination Options
% 3.21/1.00  
% 3.21/1.00  --comb_res_mult                         3
% 3.21/1.00  --comb_sup_mult                         2
% 3.21/1.00  --comb_inst_mult                        10
% 3.21/1.00  
% 3.21/1.00  ------ Debug Options
% 3.21/1.00  
% 3.21/1.00  --dbg_backtrace                         false
% 3.21/1.00  --dbg_dump_prop_clauses                 false
% 3.21/1.00  --dbg_dump_prop_clauses_file            -
% 3.21/1.00  --dbg_out_stat                          false
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  ------ Proving...
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS status Theorem for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  fof(f1,axiom,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f16,plain,(
% 3.21/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f1])).
% 3.21/1.00  
% 3.21/1.00  fof(f31,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(nnf_transformation,[],[f16])).
% 3.21/1.00  
% 3.21/1.00  fof(f32,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(rectify,[],[f31])).
% 3.21/1.00  
% 3.21/1.00  fof(f33,plain,(
% 3.21/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f34,plain,(
% 3.21/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.21/1.00  
% 3.21/1.00  fof(f43,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f34])).
% 3.21/1.00  
% 3.21/1.00  fof(f5,axiom,(
% 3.21/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f52,plain,(
% 3.21/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f5])).
% 3.21/1.00  
% 3.21/1.00  fof(f13,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f27,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.21/1.00    inference(ennf_transformation,[],[f13])).
% 3.21/1.00  
% 3.21/1.00  fof(f28,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.21/1.00    inference(flattening,[],[f27])).
% 3.21/1.00  
% 3.21/1.00  fof(f63,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f28])).
% 3.21/1.00  
% 3.21/1.00  fof(f12,axiom,(
% 3.21/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => r2_hidden(X1,k1_funct_2(X0,X0)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f25,plain,(
% 3.21/1.00    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.21/1.00    inference(ennf_transformation,[],[f12])).
% 3.21/1.00  
% 3.21/1.00  fof(f26,plain,(
% 3.21/1.00    ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.21/1.00    inference(flattening,[],[f25])).
% 3.21/1.00  
% 3.21/1.00  fof(f61,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_funct_2(X0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f26])).
% 3.21/1.00  
% 3.21/1.00  fof(f62,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f28])).
% 3.21/1.00  
% 3.21/1.00  fof(f64,plain,(
% 3.21/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f28])).
% 3.21/1.00  
% 3.21/1.00  fof(f14,conjecture,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f15,negated_conjecture,(
% 3.21/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 3.21/1.00    inference(negated_conjecture,[],[f14])).
% 3.21/1.00  
% 3.21/1.00  fof(f29,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.21/1.00    inference(ennf_transformation,[],[f15])).
% 3.21/1.00  
% 3.21/1.00  fof(f30,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.21/1.00    inference(flattening,[],[f29])).
% 3.21/1.00  
% 3.21/1.00  fof(f40,plain,(
% 3.21/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 3.21/1.00    introduced(choice_axiom,[])).
% 3.21/1.00  
% 3.21/1.00  fof(f41,plain,(
% 3.21/1.00    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 3.21/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f40])).
% 3.21/1.00  
% 3.21/1.00  fof(f65,plain,(
% 3.21/1.00    v1_funct_1(sK3)),
% 3.21/1.00    inference(cnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f4,axiom,(
% 3.21/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f37,plain,(
% 3.21/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/1.00    inference(nnf_transformation,[],[f4])).
% 3.21/1.00  
% 3.21/1.00  fof(f38,plain,(
% 3.21/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/1.00    inference(flattening,[],[f37])).
% 3.21/1.00  
% 3.21/1.00  fof(f49,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f50,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.21/1.00    inference(cnf_transformation,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f71,plain,(
% 3.21/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.21/1.00    inference(equality_resolution,[],[f50])).
% 3.21/1.00  
% 3.21/1.00  fof(f2,axiom,(
% 3.21/1.00    v1_xboole_0(k1_xboole_0)),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f45,plain,(
% 3.21/1.00    v1_xboole_0(k1_xboole_0)),
% 3.21/1.00    inference(cnf_transformation,[],[f2])).
% 3.21/1.00  
% 3.21/1.00  fof(f66,plain,(
% 3.21/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.21/1.00    inference(cnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f11,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f23,plain,(
% 3.21/1.00    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.21/1.00    inference(ennf_transformation,[],[f11])).
% 3.21/1.00  
% 3.21/1.00  fof(f24,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.21/1.00    inference(flattening,[],[f23])).
% 3.21/1.00  
% 3.21/1.00  fof(f59,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f24])).
% 3.21/1.00  
% 3.21/1.00  fof(f44,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f34])).
% 3.21/1.00  
% 3.21/1.00  fof(f67,plain,(
% 3.21/1.00    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))),
% 3.21/1.00    inference(cnf_transformation,[],[f41])).
% 3.21/1.00  
% 3.21/1.00  fof(f3,axiom,(
% 3.21/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f35,plain,(
% 3.21/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/1.00    inference(nnf_transformation,[],[f3])).
% 3.21/1.00  
% 3.21/1.00  fof(f36,plain,(
% 3.21/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.21/1.00    inference(flattening,[],[f35])).
% 3.21/1.00  
% 3.21/1.00  fof(f47,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.21/1.00    inference(cnf_transformation,[],[f36])).
% 3.21/1.00  
% 3.21/1.00  fof(f68,plain,(
% 3.21/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.21/1.00    inference(equality_resolution,[],[f47])).
% 3.21/1.00  
% 3.21/1.00  fof(f8,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f19,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.21/1.00    inference(ennf_transformation,[],[f8])).
% 3.21/1.00  
% 3.21/1.00  fof(f56,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f19])).
% 3.21/1.00  
% 3.21/1.00  fof(f6,axiom,(
% 3.21/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f39,plain,(
% 3.21/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.21/1.00    inference(nnf_transformation,[],[f6])).
% 3.21/1.00  
% 3.21/1.00  fof(f54,plain,(
% 3.21/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f39])).
% 3.21/1.00  
% 3.21/1.00  fof(f53,plain,(
% 3.21/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.21/1.00    inference(cnf_transformation,[],[f39])).
% 3.21/1.00  
% 3.21/1.00  fof(f48,plain,(
% 3.21/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f36])).
% 3.21/1.00  
% 3.21/1.00  fof(f51,plain,(
% 3.21/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.21/1.00    inference(cnf_transformation,[],[f38])).
% 3.21/1.00  
% 3.21/1.00  fof(f70,plain,(
% 3.21/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.21/1.00    inference(equality_resolution,[],[f51])).
% 3.21/1.00  
% 3.21/1.00  fof(f10,axiom,(
% 3.21/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 3.21/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/1.00  
% 3.21/1.00  fof(f21,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.21/1.00    inference(ennf_transformation,[],[f10])).
% 3.21/1.00  
% 3.21/1.00  fof(f22,plain,(
% 3.21/1.00    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.21/1.00    inference(flattening,[],[f21])).
% 3.21/1.00  
% 3.21/1.00  fof(f58,plain,(
% 3.21/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.21/1.00    inference(cnf_transformation,[],[f22])).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1119,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_10,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1114,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_21,plain,
% 3.21/1.00      ( v1_funct_2(X0,X1,X2)
% 3.21/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 3.21/1.00      | ~ v1_funct_1(X3) ),
% 3.21/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_19,plain,
% 3.21/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(X1,X1))
% 3.21/1.00      | ~ v1_funct_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_348,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
% 3.21/1.00      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | r2_hidden(X3,k1_funct_2(X4,X4))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_funct_1(X3)
% 3.21/1.00      | X4 != X2
% 3.21/1.00      | X4 != X1
% 3.21/1.00      | X3 != X5 ),
% 3.21/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_19]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_349,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/1.00      | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
% 3.21/1.00      | r2_hidden(X2,k1_funct_2(X1,X1))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_funct_1(X2) ),
% 3.21/1.00      inference(unflattening,[status(thm)],[c_348]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_22,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | v1_funct_1(X3) ),
% 3.21/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_20,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | ~ v1_funct_1(X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_363,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.21/1.00      | ~ r2_hidden(X2,k5_partfun1(X1,X1,X0))
% 3.21/1.00      | r2_hidden(X2,k1_funct_2(X1,X1))
% 3.21/1.00      | ~ v1_funct_1(X0) ),
% 3.21/1.00      inference(forward_subsumption_resolution,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_349,c_22,c_20]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1100,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.21/1.00      | r2_hidden(X2,k5_partfun1(X1,X1,X0)) != iProver_top
% 3.21/1.00      | r2_hidden(X2,k1_funct_2(X1,X1)) = iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2001,plain,
% 3.21/1.00      ( r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top
% 3.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1114,c_1100]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_25,negated_conjecture,
% 3.21/1.00      ( v1_funct_1(sK3) ),
% 3.21/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_26,plain,
% 3.21/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_9,plain,
% 3.21/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 = X1
% 3.21/1.00      | k1_xboole_0 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_56,plain,
% 3.21/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_8,plain,
% 3.21/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_57,plain,
% 3.21/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3,plain,
% 3.21/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_65,plain,
% 3.21/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_585,plain,
% 3.21/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1298,plain,
% 3.21/1.00      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_585]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1299,plain,
% 3.21/1.00      ( X0 != sK3
% 3.21/1.00      | v1_funct_1(X0) = iProver_top
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1301,plain,
% 3.21/1.00      ( k1_xboole_0 != sK3
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top
% 3.21/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1299]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_577,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1379,plain,
% 3.21/1.00      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_577]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1380,plain,
% 3.21/1.00      ( sK3 != k1_xboole_0
% 3.21/1.00      | k1_xboole_0 = sK3
% 3.21/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1379]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_24,negated_conjecture,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.21/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1105,plain,
% 3.21/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_18,plain,
% 3.21/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(X1,X2))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_301,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.21/1.00      | ~ v1_funct_1(X3)
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(resolution,[status(thm)],[c_21,c_18]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_305,plain,
% 3.21/1.00      ( r2_hidden(X3,k1_funct_2(X1,X2))
% 3.21/1.00      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_301,c_22,c_20]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_306,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 3.21/1.00      | r2_hidden(X3,k1_funct_2(X1,X2))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | k1_xboole_0 = X2 ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_305]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1102,plain,
% 3.21/1.00      ( k1_xboole_0 = X0
% 3.21/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.21/1.00      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 3.21/1.00      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 3.21/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2805,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 3.21/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1105,c_1102]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3273,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 3.21/1.00      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 3.21/1.00      | sK2 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2805,c_26]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3274,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_3273]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3282,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1119,c_3274]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_0,plain,
% 3.21/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1120,plain,
% 3.21/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3391,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3282,c_1120]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_23,negated_conjecture,
% 3.21/1.00      ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_28,plain,
% 3.21/1.00      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3527,plain,
% 3.21/1.00      ( sK2 = k1_xboole_0 ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_3391,c_28]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5,plain,
% 3.21/1.00      ( r1_tarski(X0,X0) ),
% 3.21/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1115,plain,
% 3.21/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_14,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/1.00      | ~ r2_hidden(X2,X0)
% 3.21/1.00      | ~ v1_xboole_0(X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_11,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_166,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.21/1.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_167,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_166]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_219,plain,
% 3.21/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.21/1.00      inference(bin_hyper_res,[status(thm)],[c_14,c_167]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1103,plain,
% 3.21/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.21/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.21/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2579,plain,
% 3.21/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X2) = iProver_top
% 3.21/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1119,c_1103]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2657,plain,
% 3.21/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1115,c_2579]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_12,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.21/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1112,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1504,plain,
% 3.21/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1105,c_1112]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1116,plain,
% 3.21/1.00      ( X0 = X1
% 3.21/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.21/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1891,plain,
% 3.21/1.00      ( k2_zfmisc_1(sK1,sK2) = sK3
% 3.21/1.00      | r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1504,c_1116]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2776,plain,
% 3.21/1.00      ( k2_zfmisc_1(sK1,sK2) = sK3
% 3.21/1.00      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2657,c_1891]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3530,plain,
% 3.21/1.00      ( k2_zfmisc_1(sK1,k1_xboole_0) = sK3
% 3.21/1.00      | v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3527,c_2776]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7,plain,
% 3.21/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3580,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3530,c_7]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4949,plain,
% 3.21/1.00      ( r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top
% 3.21/1.00      | r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_2001,c_26,c_56,c_57,c_65,c_1301,c_1380,c_3580]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4950,plain,
% 3.21/1.00      ( r2_hidden(X0,k5_partfun1(X1,X1,k1_xboole_0)) != iProver_top
% 3.21/1.00      | r2_hidden(X0,k1_funct_2(X1,X1)) = iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_4949]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4957,plain,
% 3.21/1.00      ( r2_hidden(sK0(k5_partfun1(X0,X0,k1_xboole_0),X1),k1_funct_2(X0,X0)) = iProver_top
% 3.21/1.00      | r1_tarski(k5_partfun1(X0,X0,k1_xboole_0),X1) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1119,c_4950]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7131,plain,
% 3.21/1.00      ( r1_tarski(k5_partfun1(X0,X0,k1_xboole_0),k1_funct_2(X0,X0)) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4957,c_1120]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_7156,plain,
% 3.21/1.00      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_7131]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_16,plain,
% 3.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/1.00      | ~ v1_funct_1(X0)
% 3.21/1.00      | ~ v1_xboole_0(X2)
% 3.21/1.00      | v1_xboole_0(X1)
% 3.21/1.00      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 3.21/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1109,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_xboole_0(X2) != iProver_top
% 3.21/1.00      | v1_xboole_0(X1) = iProver_top
% 3.21/1.00      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4153,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_xboole_0(X1) = iProver_top
% 3.21/1.00      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 3.21/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_7,c_1109]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4962,plain,
% 3.21/1.00      ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top
% 3.21/1.00      | v1_xboole_0(X1) = iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4153,c_65]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4963,plain,
% 3.21/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.21/1.00      | v1_funct_1(X0) != iProver_top
% 3.21/1.00      | v1_xboole_0(X1) = iProver_top
% 3.21/1.00      | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X0)) = iProver_top ),
% 3.21/1.00      inference(renaming,[status(thm)],[c_4962]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3538,plain,
% 3.21/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3527,c_1504]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3547,plain,
% 3.21/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3538,c_7]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1503,plain,
% 3.21/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1114,c_1112]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1890,plain,
% 3.21/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_1503,c_1116]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3712,plain,
% 3.21/1.00      ( sK3 = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_3547,c_1890]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1106,plain,
% 3.21/1.00      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2773,plain,
% 3.21/1.00      ( v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2657,c_1106]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_3533,plain,
% 3.21/1.00      ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,sK3)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3527,c_2773]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4317,plain,
% 3.21/1.00      ( v1_xboole_0(k5_partfun1(sK1,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(demodulation,[status(thm)],[c_3712,c_3533]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_4970,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.21/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.21/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_4963,c_4317]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_53,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_55,plain,
% 3.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_53]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5364,plain,
% 3.21/1.00      ( v1_xboole_0(sK1) = iProver_top ),
% 3.21/1.00      inference(global_propositional_subsumption,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_4970,c_26,c_55,c_56,c_57,c_65,c_1301,c_1380,c_3580]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_2775,plain,
% 3.21/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_2657,c_1890]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_5374,plain,
% 3.21/1.00      ( sK1 = k1_xboole_0 ),
% 3.21/1.00      inference(superposition,[status(thm)],[c_5364,c_2775]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_584,plain,
% 3.21/1.00      ( X0 != X1
% 3.21/1.00      | X2 != X3
% 3.21/1.00      | X4 != X5
% 3.21/1.00      | k5_partfun1(X0,X2,X4) = k5_partfun1(X1,X3,X5) ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1713,plain,
% 3.21/1.00      ( k5_partfun1(sK1,sK2,sK3) = k5_partfun1(X0,X1,X2)
% 3.21/1.00      | sK3 != X2
% 3.21/1.00      | sK2 != X1
% 3.21/1.00      | sK1 != X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_584]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1718,plain,
% 3.21/1.00      ( k5_partfun1(sK1,sK2,sK3) = k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.21/1.00      | sK3 != k1_xboole_0
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1713]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_578,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1318,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,X1)
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
% 3.21/1.00      | k5_partfun1(sK1,sK2,sK3) != X0
% 3.21/1.00      | k1_funct_2(sK1,sK2) != X1 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_578]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1397,plain,
% 3.21/1.00      ( ~ r1_tarski(X0,k1_funct_2(X1,X2))
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
% 3.21/1.00      | k5_partfun1(sK1,sK2,sK3) != X0
% 3.21/1.00      | k1_funct_2(sK1,sK2) != k1_funct_2(X1,X2) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1318]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1712,plain,
% 3.21/1.00      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4))
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
% 3.21/1.00      | k5_partfun1(sK1,sK2,sK3) != k5_partfun1(X0,X1,X2)
% 3.21/1.00      | k1_funct_2(sK1,sK2) != k1_funct_2(X3,X4) ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1397]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1714,plain,
% 3.21/1.00      ( k5_partfun1(sK1,sK2,sK3) != k5_partfun1(X0,X1,X2)
% 3.21/1.00      | k1_funct_2(sK1,sK2) != k1_funct_2(X3,X4)
% 3.21/1.00      | r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X3,X4)) != iProver_top
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
% 3.21/1.00      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1716,plain,
% 3.21/1.00      ( k5_partfun1(sK1,sK2,sK3) != k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.21/1.00      | k1_funct_2(sK1,sK2) != k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.21/1.00      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top
% 3.21/1.00      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1714]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_586,plain,
% 3.21/1.00      ( X0 != X1 | X2 != X3 | k1_funct_2(X0,X2) = k1_funct_2(X1,X3) ),
% 3.21/1.00      theory(equality) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1398,plain,
% 3.21/1.00      ( k1_funct_2(sK1,sK2) = k1_funct_2(X0,X1) | sK2 != X1 | sK1 != X0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_586]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(c_1403,plain,
% 3.21/1.00      ( k1_funct_2(sK1,sK2) = k1_funct_2(k1_xboole_0,k1_xboole_0)
% 3.21/1.00      | sK2 != k1_xboole_0
% 3.21/1.00      | sK1 != k1_xboole_0 ),
% 3.21/1.00      inference(instantiation,[status(thm)],[c_1398]) ).
% 3.21/1.00  
% 3.21/1.00  cnf(contradiction,plain,
% 3.21/1.00      ( $false ),
% 3.21/1.00      inference(minisat,
% 3.21/1.00                [status(thm)],
% 3.21/1.00                [c_7156,c_5374,c_3580,c_3391,c_1718,c_1716,c_1403,c_65,
% 3.21/1.00                 c_28]) ).
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.00  
% 3.21/1.00  ------                               Statistics
% 3.21/1.00  
% 3.21/1.00  ------ General
% 3.21/1.00  
% 3.21/1.00  abstr_ref_over_cycles:                  0
% 3.21/1.00  abstr_ref_under_cycles:                 0
% 3.21/1.00  gc_basic_clause_elim:                   0
% 3.21/1.00  forced_gc_time:                         0
% 3.21/1.00  parsing_time:                           0.009
% 3.21/1.00  unif_index_cands_time:                  0.
% 3.21/1.00  unif_index_add_time:                    0.
% 3.21/1.00  orderings_time:                         0.
% 3.21/1.00  out_proof_time:                         0.014
% 3.21/1.00  total_time:                             0.274
% 3.21/1.00  num_of_symbols:                         46
% 3.21/1.00  num_of_terms:                           5803
% 3.21/1.00  
% 3.21/1.00  ------ Preprocessing
% 3.21/1.00  
% 3.21/1.00  num_of_splits:                          0
% 3.21/1.00  num_of_split_atoms:                     0
% 3.21/1.00  num_of_reused_defs:                     0
% 3.21/1.00  num_eq_ax_congr_red:                    8
% 3.21/1.00  num_of_sem_filtered_clauses:            1
% 3.21/1.00  num_of_subtypes:                        0
% 3.21/1.00  monotx_restored_types:                  0
% 3.21/1.00  sat_num_of_epr_types:                   0
% 3.21/1.00  sat_num_of_non_cyclic_types:            0
% 3.21/1.00  sat_guarded_non_collapsed_types:        0
% 3.21/1.00  num_pure_diseq_elim:                    0
% 3.21/1.00  simp_replaced_by:                       0
% 3.21/1.00  res_preprocessed:                       120
% 3.21/1.00  prep_upred:                             0
% 3.21/1.00  prep_unflattend:                        6
% 3.21/1.00  smt_new_axioms:                         0
% 3.21/1.00  pred_elim_cands:                        5
% 3.21/1.00  pred_elim:                              1
% 3.21/1.00  pred_elim_cl:                           1
% 3.21/1.00  pred_elim_cycles:                       3
% 3.21/1.00  merged_defs:                            8
% 3.21/1.00  merged_defs_ncl:                        0
% 3.21/1.00  bin_hyper_res:                          9
% 3.21/1.00  prep_cycles:                            4
% 3.21/1.00  pred_elim_time:                         0.003
% 3.21/1.00  splitting_time:                         0.
% 3.21/1.00  sem_filter_time:                        0.
% 3.21/1.00  monotx_time:                            0.001
% 3.21/1.00  subtype_inf_time:                       0.
% 3.21/1.00  
% 3.21/1.00  ------ Problem properties
% 3.21/1.00  
% 3.21/1.00  clauses:                                24
% 3.21/1.00  conjectures:                            3
% 3.21/1.00  epr:                                    6
% 3.21/1.00  horn:                                   20
% 3.21/1.00  ground:                                 4
% 3.21/1.00  unary:                                  8
% 3.21/1.00  binary:                                 4
% 3.21/1.00  lits:                                   60
% 3.21/1.00  lits_eq:                                7
% 3.21/1.00  fd_pure:                                0
% 3.21/1.00  fd_pseudo:                              0
% 3.21/1.00  fd_cond:                                2
% 3.21/1.00  fd_pseudo_cond:                         1
% 3.21/1.00  ac_symbols:                             0
% 3.21/1.00  
% 3.21/1.00  ------ Propositional Solver
% 3.21/1.00  
% 3.21/1.00  prop_solver_calls:                      29
% 3.21/1.00  prop_fast_solver_calls:                 900
% 3.21/1.00  smt_solver_calls:                       0
% 3.21/1.00  smt_fast_solver_calls:                  0
% 3.21/1.00  prop_num_of_clauses:                    2382
% 3.21/1.00  prop_preprocess_simplified:             7118
% 3.21/1.00  prop_fo_subsumed:                       15
% 3.21/1.00  prop_solver_time:                       0.
% 3.21/1.00  smt_solver_time:                        0.
% 3.21/1.00  smt_fast_solver_time:                   0.
% 3.21/1.00  prop_fast_solver_time:                  0.
% 3.21/1.00  prop_unsat_core_time:                   0.
% 3.21/1.00  
% 3.21/1.00  ------ QBF
% 3.21/1.00  
% 3.21/1.00  qbf_q_res:                              0
% 3.21/1.00  qbf_num_tautologies:                    0
% 3.21/1.00  qbf_prep_cycles:                        0
% 3.21/1.00  
% 3.21/1.00  ------ BMC1
% 3.21/1.00  
% 3.21/1.00  bmc1_current_bound:                     -1
% 3.21/1.00  bmc1_last_solved_bound:                 -1
% 3.21/1.00  bmc1_unsat_core_size:                   -1
% 3.21/1.00  bmc1_unsat_core_parents_size:           -1
% 3.21/1.00  bmc1_merge_next_fun:                    0
% 3.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.00  
% 3.21/1.00  ------ Instantiation
% 3.21/1.00  
% 3.21/1.00  inst_num_of_clauses:                    736
% 3.21/1.00  inst_num_in_passive:                    311
% 3.21/1.00  inst_num_in_active:                     312
% 3.21/1.00  inst_num_in_unprocessed:                113
% 3.21/1.00  inst_num_of_loops:                      450
% 3.21/1.00  inst_num_of_learning_restarts:          0
% 3.21/1.00  inst_num_moves_active_passive:          135
% 3.21/1.00  inst_lit_activity:                      0
% 3.21/1.00  inst_lit_activity_moves:                0
% 3.21/1.00  inst_num_tautologies:                   0
% 3.21/1.00  inst_num_prop_implied:                  0
% 3.21/1.00  inst_num_existing_simplified:           0
% 3.21/1.00  inst_num_eq_res_simplified:             0
% 3.21/1.00  inst_num_child_elim:                    0
% 3.21/1.00  inst_num_of_dismatching_blockings:      278
% 3.21/1.00  inst_num_of_non_proper_insts:           767
% 3.21/1.00  inst_num_of_duplicates:                 0
% 3.21/1.00  inst_inst_num_from_inst_to_res:         0
% 3.21/1.00  inst_dismatching_checking_time:         0.
% 3.21/1.00  
% 3.21/1.00  ------ Resolution
% 3.21/1.00  
% 3.21/1.00  res_num_of_clauses:                     0
% 3.21/1.00  res_num_in_passive:                     0
% 3.21/1.00  res_num_in_active:                      0
% 3.21/1.00  res_num_of_loops:                       124
% 3.21/1.00  res_forward_subset_subsumed:            115
% 3.21/1.00  res_backward_subset_subsumed:           0
% 3.21/1.00  res_forward_subsumed:                   0
% 3.21/1.00  res_backward_subsumed:                  0
% 3.21/1.00  res_forward_subsumption_resolution:     4
% 3.21/1.00  res_backward_subsumption_resolution:    0
% 3.21/1.00  res_clause_to_clause_subsumption:       519
% 3.21/1.00  res_orphan_elimination:                 0
% 3.21/1.00  res_tautology_del:                      56
% 3.21/1.00  res_num_eq_res_simplified:              0
% 3.21/1.00  res_num_sel_changes:                    0
% 3.21/1.00  res_moves_from_active_to_pass:          0
% 3.21/1.00  
% 3.21/1.00  ------ Superposition
% 3.21/1.00  
% 3.21/1.00  sup_time_total:                         0.
% 3.21/1.00  sup_time_generating:                    0.
% 3.21/1.00  sup_time_sim_full:                      0.
% 3.21/1.00  sup_time_sim_immed:                     0.
% 3.21/1.00  
% 3.21/1.00  sup_num_of_clauses:                     114
% 3.21/1.00  sup_num_in_active:                      62
% 3.21/1.00  sup_num_in_passive:                     52
% 3.21/1.00  sup_num_of_loops:                       89
% 3.21/1.00  sup_fw_superposition:                   109
% 3.21/1.00  sup_bw_superposition:                   49
% 3.21/1.00  sup_immediate_simplified:               26
% 3.21/1.00  sup_given_eliminated:                   1
% 3.21/1.00  comparisons_done:                       0
% 3.21/1.00  comparisons_avoided:                    0
% 3.21/1.00  
% 3.21/1.00  ------ Simplifications
% 3.21/1.00  
% 3.21/1.00  
% 3.21/1.00  sim_fw_subset_subsumed:                 7
% 3.21/1.00  sim_bw_subset_subsumed:                 6
% 3.21/1.00  sim_fw_subsumed:                        9
% 3.21/1.00  sim_bw_subsumed:                        0
% 3.21/1.00  sim_fw_subsumption_res:                 0
% 3.21/1.00  sim_bw_subsumption_res:                 0
% 3.21/1.00  sim_tautology_del:                      4
% 3.21/1.00  sim_eq_tautology_del:                   5
% 3.21/1.00  sim_eq_res_simp:                        0
% 3.21/1.00  sim_fw_demodulated:                     14
% 3.21/1.00  sim_bw_demodulated:                     26
% 3.21/1.00  sim_light_normalised:                   1
% 3.21/1.00  sim_joinable_taut:                      0
% 3.21/1.00  sim_joinable_simp:                      0
% 3.21/1.00  sim_ac_normalised:                      0
% 3.21/1.00  sim_smt_subsumption:                    0
% 3.21/1.00  
%------------------------------------------------------------------------------
