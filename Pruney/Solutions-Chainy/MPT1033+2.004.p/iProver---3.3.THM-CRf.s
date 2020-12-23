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
% DateTime   : Thu Dec  3 12:08:29 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  145 (1414 expanded)
%              Number of clauses        :   94 ( 423 expanded)
%              Number of leaves         :   14 ( 353 expanded)
%              Depth                    :   23
%              Number of atoms          :  475 (10020 expanded)
%              Number of equality atoms :  183 (2368 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK5)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK5,X0,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK2,sK3,sK4,X3)
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & r1_partfun1(sK4,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5)
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_partfun1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f48,f47])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f45])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1150,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2342,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(X1,sK5)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_5142,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(sK4,sK5)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_5144,plain,
    ( r1_tarski(sK4,sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5142])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1688,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_549,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | sK1(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_550,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_587,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X2 != X3
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_550,c_20])).

cnf(c_588,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_655,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_588,c_33])).

cnf(c_656,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_658,plain,
    ( v1_partfun1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_656,c_34,c_32])).

cnf(c_1682,plain,
    ( k1_xboole_0 = sK3
    | v1_partfun1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_641,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_588,c_30])).

cnf(c_642,plain,
    ( v1_partfun1(sK5,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_644,plain,
    ( v1_partfun1(sK5,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_31,c_29])).

cnf(c_1683,plain,
    ( k1_xboole_0 = sK3
    | v1_partfun1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_22,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_456,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK5 != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_457,plain,
    ( ~ v1_partfun1(sK5,X0)
    | ~ v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | sK5 = sK4 ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_461,plain,
    ( ~ v1_partfun1(sK5,X0)
    | ~ v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_34,c_31])).

cnf(c_1684,plain,
    ( sK5 = sK4
    | v1_partfun1(sK5,X0) != iProver_top
    | v1_partfun1(sK4,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_2206,plain,
    ( sK5 = sK4
    | v1_partfun1(sK5,sK2) != iProver_top
    | v1_partfun1(sK4,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1684])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2375,plain,
    ( v1_partfun1(sK4,sK2) != iProver_top
    | v1_partfun1(sK5,sK2) != iProver_top
    | sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2206,c_37])).

cnf(c_2376,plain,
    ( sK5 = sK4
    | v1_partfun1(sK5,sK2) != iProver_top
    | v1_partfun1(sK4,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2375])).

cnf(c_2521,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0
    | v1_partfun1(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_2376])).

cnf(c_3461,plain,
    ( sK5 = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1682,c_2521])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK5 != X0
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK4 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_29])).

cnf(c_1686,plain,
    ( sK4 != sK5
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_4342,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_1686])).

cnf(c_4410,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1688,c_4342])).

cnf(c_4585,plain,
    ( sK5 != sK4
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4410,c_1686])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4588,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4410,c_27])).

cnf(c_4589,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4588])).

cnf(c_4600,plain,
    ( sK5 != sK4
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4585,c_4589])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4603,plain,
    ( sK5 != sK4
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4600,c_5])).

cnf(c_4617,plain,
    ( sK5 != sK4
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4603])).

cnf(c_4586,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4410,c_1688])).

cnf(c_4596,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4586,c_4589])).

cnf(c_4598,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4596,c_5])).

cnf(c_1687,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4587,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4410,c_1687])).

cnf(c_4592,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4587,c_4589])).

cnf(c_4594,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4592,c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2014,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4247,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r1_tarski(sK4,sK5)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2935,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2938,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_2884,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2885,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2884])).

cnf(c_2682,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2683,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2682])).

cnf(c_2685,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2683])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2639,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2640,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2639])).

cnf(c_2642,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2640])).

cnf(c_2580,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2581,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_2583,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2337,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_2339,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2337])).

cnf(c_2338,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5))
    | r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_2336])).

cnf(c_2312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2312])).

cnf(c_2315,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_2314,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
    | r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_2015,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_2017,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2009,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(sK5,sK4)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_2011,plain,
    ( r1_tarski(sK5,sK4)
    | ~ r1_tarski(k1_xboole_0,sK4)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2009])).

cnf(c_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_90,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5144,c_4617,c_4598,c_4594,c_4247,c_2938,c_2935,c_2885,c_2884,c_2685,c_2642,c_2583,c_2339,c_2338,c_2315,c_2314,c_2017,c_2011,c_90])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.34/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.06  
% 2.34/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/1.06  
% 2.34/1.06  ------  iProver source info
% 2.34/1.06  
% 2.34/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.34/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/1.06  git: non_committed_changes: false
% 2.34/1.06  git: last_make_outside_of_git: false
% 2.34/1.06  
% 2.34/1.06  ------ 
% 2.34/1.06  
% 2.34/1.06  ------ Input Options
% 2.34/1.06  
% 2.34/1.06  --out_options                           all
% 2.34/1.06  --tptp_safe_out                         true
% 2.34/1.06  --problem_path                          ""
% 2.34/1.06  --include_path                          ""
% 2.34/1.06  --clausifier                            res/vclausify_rel
% 2.34/1.06  --clausifier_options                    --mode clausify
% 2.34/1.06  --stdin                                 false
% 2.34/1.06  --stats_out                             all
% 2.34/1.06  
% 2.34/1.06  ------ General Options
% 2.34/1.06  
% 2.34/1.06  --fof                                   false
% 2.34/1.06  --time_out_real                         305.
% 2.34/1.06  --time_out_virtual                      -1.
% 2.34/1.06  --symbol_type_check                     false
% 2.34/1.06  --clausify_out                          false
% 2.34/1.06  --sig_cnt_out                           false
% 2.34/1.06  --trig_cnt_out                          false
% 2.34/1.06  --trig_cnt_out_tolerance                1.
% 2.34/1.06  --trig_cnt_out_sk_spl                   false
% 2.34/1.06  --abstr_cl_out                          false
% 2.34/1.06  
% 2.34/1.06  ------ Global Options
% 2.34/1.06  
% 2.34/1.06  --schedule                              default
% 2.34/1.06  --add_important_lit                     false
% 2.34/1.06  --prop_solver_per_cl                    1000
% 2.34/1.06  --min_unsat_core                        false
% 2.34/1.06  --soft_assumptions                      false
% 2.34/1.06  --soft_lemma_size                       3
% 2.34/1.06  --prop_impl_unit_size                   0
% 2.34/1.06  --prop_impl_unit                        []
% 2.34/1.06  --share_sel_clauses                     true
% 2.34/1.06  --reset_solvers                         false
% 2.34/1.06  --bc_imp_inh                            [conj_cone]
% 2.34/1.06  --conj_cone_tolerance                   3.
% 2.34/1.06  --extra_neg_conj                        none
% 2.34/1.06  --large_theory_mode                     true
% 2.34/1.06  --prolific_symb_bound                   200
% 2.34/1.06  --lt_threshold                          2000
% 2.34/1.06  --clause_weak_htbl                      true
% 2.34/1.06  --gc_record_bc_elim                     false
% 2.34/1.06  
% 2.34/1.06  ------ Preprocessing Options
% 2.34/1.06  
% 2.34/1.06  --preprocessing_flag                    true
% 2.34/1.06  --time_out_prep_mult                    0.1
% 2.34/1.06  --splitting_mode                        input
% 2.34/1.06  --splitting_grd                         true
% 2.34/1.06  --splitting_cvd                         false
% 2.34/1.06  --splitting_cvd_svl                     false
% 2.34/1.06  --splitting_nvd                         32
% 2.34/1.06  --sub_typing                            true
% 2.34/1.06  --prep_gs_sim                           true
% 2.34/1.06  --prep_unflatten                        true
% 2.34/1.06  --prep_res_sim                          true
% 2.34/1.06  --prep_upred                            true
% 2.34/1.06  --prep_sem_filter                       exhaustive
% 2.34/1.06  --prep_sem_filter_out                   false
% 2.34/1.06  --pred_elim                             true
% 2.34/1.06  --res_sim_input                         true
% 2.34/1.06  --eq_ax_congr_red                       true
% 2.34/1.06  --pure_diseq_elim                       true
% 2.34/1.06  --brand_transform                       false
% 2.34/1.06  --non_eq_to_eq                          false
% 2.34/1.06  --prep_def_merge                        true
% 2.34/1.06  --prep_def_merge_prop_impl              false
% 2.34/1.06  --prep_def_merge_mbd                    true
% 2.34/1.06  --prep_def_merge_tr_red                 false
% 2.34/1.06  --prep_def_merge_tr_cl                  false
% 2.34/1.06  --smt_preprocessing                     true
% 2.34/1.06  --smt_ac_axioms                         fast
% 2.34/1.06  --preprocessed_out                      false
% 2.34/1.06  --preprocessed_stats                    false
% 2.34/1.06  
% 2.34/1.06  ------ Abstraction refinement Options
% 2.34/1.06  
% 2.34/1.06  --abstr_ref                             []
% 2.34/1.06  --abstr_ref_prep                        false
% 2.34/1.06  --abstr_ref_until_sat                   false
% 2.34/1.06  --abstr_ref_sig_restrict                funpre
% 2.34/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.06  --abstr_ref_under                       []
% 2.34/1.06  
% 2.34/1.06  ------ SAT Options
% 2.34/1.06  
% 2.34/1.06  --sat_mode                              false
% 2.34/1.06  --sat_fm_restart_options                ""
% 2.34/1.06  --sat_gr_def                            false
% 2.34/1.06  --sat_epr_types                         true
% 2.34/1.06  --sat_non_cyclic_types                  false
% 2.34/1.06  --sat_finite_models                     false
% 2.34/1.06  --sat_fm_lemmas                         false
% 2.34/1.06  --sat_fm_prep                           false
% 2.34/1.06  --sat_fm_uc_incr                        true
% 2.34/1.06  --sat_out_model                         small
% 2.34/1.06  --sat_out_clauses                       false
% 2.34/1.06  
% 2.34/1.06  ------ QBF Options
% 2.34/1.06  
% 2.34/1.06  --qbf_mode                              false
% 2.34/1.06  --qbf_elim_univ                         false
% 2.34/1.06  --qbf_dom_inst                          none
% 2.34/1.06  --qbf_dom_pre_inst                      false
% 2.34/1.06  --qbf_sk_in                             false
% 2.34/1.06  --qbf_pred_elim                         true
% 2.34/1.06  --qbf_split                             512
% 2.34/1.06  
% 2.34/1.06  ------ BMC1 Options
% 2.34/1.06  
% 2.34/1.06  --bmc1_incremental                      false
% 2.34/1.06  --bmc1_axioms                           reachable_all
% 2.34/1.06  --bmc1_min_bound                        0
% 2.34/1.06  --bmc1_max_bound                        -1
% 2.34/1.06  --bmc1_max_bound_default                -1
% 2.34/1.06  --bmc1_symbol_reachability              true
% 2.34/1.06  --bmc1_property_lemmas                  false
% 2.34/1.06  --bmc1_k_induction                      false
% 2.34/1.06  --bmc1_non_equiv_states                 false
% 2.34/1.06  --bmc1_deadlock                         false
% 2.34/1.06  --bmc1_ucm                              false
% 2.34/1.06  --bmc1_add_unsat_core                   none
% 2.34/1.06  --bmc1_unsat_core_children              false
% 2.34/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.06  --bmc1_out_stat                         full
% 2.34/1.06  --bmc1_ground_init                      false
% 2.34/1.06  --bmc1_pre_inst_next_state              false
% 2.34/1.06  --bmc1_pre_inst_state                   false
% 2.34/1.06  --bmc1_pre_inst_reach_state             false
% 2.34/1.06  --bmc1_out_unsat_core                   false
% 2.34/1.06  --bmc1_aig_witness_out                  false
% 2.34/1.06  --bmc1_verbose                          false
% 2.34/1.06  --bmc1_dump_clauses_tptp                false
% 2.34/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.06  --bmc1_dump_file                        -
% 2.34/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.06  --bmc1_ucm_extend_mode                  1
% 2.34/1.06  --bmc1_ucm_init_mode                    2
% 2.34/1.06  --bmc1_ucm_cone_mode                    none
% 2.34/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.06  --bmc1_ucm_relax_model                  4
% 2.34/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.06  --bmc1_ucm_layered_model                none
% 2.34/1.06  --bmc1_ucm_max_lemma_size               10
% 2.34/1.06  
% 2.34/1.06  ------ AIG Options
% 2.34/1.06  
% 2.34/1.06  --aig_mode                              false
% 2.34/1.06  
% 2.34/1.06  ------ Instantiation Options
% 2.34/1.06  
% 2.34/1.06  --instantiation_flag                    true
% 2.34/1.06  --inst_sos_flag                         false
% 2.34/1.06  --inst_sos_phase                        true
% 2.34/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.06  --inst_lit_sel_side                     num_symb
% 2.34/1.06  --inst_solver_per_active                1400
% 2.34/1.06  --inst_solver_calls_frac                1.
% 2.34/1.06  --inst_passive_queue_type               priority_queues
% 2.34/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.06  --inst_passive_queues_freq              [25;2]
% 2.34/1.06  --inst_dismatching                      true
% 2.34/1.06  --inst_eager_unprocessed_to_passive     true
% 2.34/1.06  --inst_prop_sim_given                   true
% 2.34/1.06  --inst_prop_sim_new                     false
% 2.34/1.06  --inst_subs_new                         false
% 2.34/1.06  --inst_eq_res_simp                      false
% 2.34/1.06  --inst_subs_given                       false
% 2.34/1.06  --inst_orphan_elimination               true
% 2.34/1.06  --inst_learning_loop_flag               true
% 2.34/1.06  --inst_learning_start                   3000
% 2.34/1.06  --inst_learning_factor                  2
% 2.34/1.06  --inst_start_prop_sim_after_learn       3
% 2.34/1.06  --inst_sel_renew                        solver
% 2.34/1.06  --inst_lit_activity_flag                true
% 2.34/1.06  --inst_restr_to_given                   false
% 2.34/1.06  --inst_activity_threshold               500
% 2.34/1.06  --inst_out_proof                        true
% 2.34/1.06  
% 2.34/1.06  ------ Resolution Options
% 2.34/1.06  
% 2.34/1.06  --resolution_flag                       true
% 2.34/1.06  --res_lit_sel                           adaptive
% 2.34/1.06  --res_lit_sel_side                      none
% 2.34/1.06  --res_ordering                          kbo
% 2.34/1.06  --res_to_prop_solver                    active
% 2.34/1.06  --res_prop_simpl_new                    false
% 2.34/1.06  --res_prop_simpl_given                  true
% 2.34/1.06  --res_passive_queue_type                priority_queues
% 2.34/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.06  --res_passive_queues_freq               [15;5]
% 2.34/1.06  --res_forward_subs                      full
% 2.34/1.06  --res_backward_subs                     full
% 2.34/1.06  --res_forward_subs_resolution           true
% 2.34/1.06  --res_backward_subs_resolution          true
% 2.34/1.06  --res_orphan_elimination                true
% 2.34/1.06  --res_time_limit                        2.
% 2.34/1.06  --res_out_proof                         true
% 2.34/1.06  
% 2.34/1.06  ------ Superposition Options
% 2.34/1.06  
% 2.34/1.06  --superposition_flag                    true
% 2.34/1.06  --sup_passive_queue_type                priority_queues
% 2.34/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.06  --demod_completeness_check              fast
% 2.34/1.06  --demod_use_ground                      true
% 2.34/1.06  --sup_to_prop_solver                    passive
% 2.34/1.06  --sup_prop_simpl_new                    true
% 2.34/1.06  --sup_prop_simpl_given                  true
% 2.34/1.06  --sup_fun_splitting                     false
% 2.34/1.06  --sup_smt_interval                      50000
% 2.34/1.06  
% 2.34/1.06  ------ Superposition Simplification Setup
% 2.34/1.06  
% 2.34/1.06  --sup_indices_passive                   []
% 2.34/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_full_bw                           [BwDemod]
% 2.34/1.06  --sup_immed_triv                        [TrivRules]
% 2.34/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_immed_bw_main                     []
% 2.34/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.06  
% 2.34/1.06  ------ Combination Options
% 2.34/1.06  
% 2.34/1.06  --comb_res_mult                         3
% 2.34/1.06  --comb_sup_mult                         2
% 2.34/1.06  --comb_inst_mult                        10
% 2.34/1.06  
% 2.34/1.06  ------ Debug Options
% 2.34/1.06  
% 2.34/1.06  --dbg_backtrace                         false
% 2.34/1.06  --dbg_dump_prop_clauses                 false
% 2.34/1.06  --dbg_dump_prop_clauses_file            -
% 2.34/1.06  --dbg_out_stat                          false
% 2.34/1.06  ------ Parsing...
% 2.34/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/1.06  
% 2.34/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.34/1.06  
% 2.34/1.06  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/1.06  
% 2.34/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/1.06  ------ Proving...
% 2.34/1.06  ------ Problem Properties 
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  clauses                                 27
% 2.34/1.06  conjectures                             3
% 2.34/1.06  EPR                                     5
% 2.34/1.06  Horn                                    21
% 2.34/1.06  unary                                   7
% 2.34/1.06  binary                                  10
% 2.34/1.06  lits                                    59
% 2.34/1.06  lits eq                                 19
% 2.34/1.06  fd_pure                                 0
% 2.34/1.06  fd_pseudo                               0
% 2.34/1.06  fd_cond                                 6
% 2.34/1.06  fd_pseudo_cond                          1
% 2.34/1.06  AC symbols                              0
% 2.34/1.06  
% 2.34/1.06  ------ Schedule dynamic 5 is on 
% 2.34/1.06  
% 2.34/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  ------ 
% 2.34/1.06  Current options:
% 2.34/1.06  ------ 
% 2.34/1.06  
% 2.34/1.06  ------ Input Options
% 2.34/1.06  
% 2.34/1.06  --out_options                           all
% 2.34/1.06  --tptp_safe_out                         true
% 2.34/1.06  --problem_path                          ""
% 2.34/1.06  --include_path                          ""
% 2.34/1.06  --clausifier                            res/vclausify_rel
% 2.34/1.06  --clausifier_options                    --mode clausify
% 2.34/1.06  --stdin                                 false
% 2.34/1.06  --stats_out                             all
% 2.34/1.06  
% 2.34/1.06  ------ General Options
% 2.34/1.06  
% 2.34/1.06  --fof                                   false
% 2.34/1.06  --time_out_real                         305.
% 2.34/1.06  --time_out_virtual                      -1.
% 2.34/1.06  --symbol_type_check                     false
% 2.34/1.06  --clausify_out                          false
% 2.34/1.06  --sig_cnt_out                           false
% 2.34/1.06  --trig_cnt_out                          false
% 2.34/1.06  --trig_cnt_out_tolerance                1.
% 2.34/1.06  --trig_cnt_out_sk_spl                   false
% 2.34/1.06  --abstr_cl_out                          false
% 2.34/1.06  
% 2.34/1.06  ------ Global Options
% 2.34/1.06  
% 2.34/1.06  --schedule                              default
% 2.34/1.06  --add_important_lit                     false
% 2.34/1.06  --prop_solver_per_cl                    1000
% 2.34/1.06  --min_unsat_core                        false
% 2.34/1.06  --soft_assumptions                      false
% 2.34/1.06  --soft_lemma_size                       3
% 2.34/1.06  --prop_impl_unit_size                   0
% 2.34/1.06  --prop_impl_unit                        []
% 2.34/1.06  --share_sel_clauses                     true
% 2.34/1.06  --reset_solvers                         false
% 2.34/1.06  --bc_imp_inh                            [conj_cone]
% 2.34/1.06  --conj_cone_tolerance                   3.
% 2.34/1.06  --extra_neg_conj                        none
% 2.34/1.06  --large_theory_mode                     true
% 2.34/1.06  --prolific_symb_bound                   200
% 2.34/1.06  --lt_threshold                          2000
% 2.34/1.06  --clause_weak_htbl                      true
% 2.34/1.06  --gc_record_bc_elim                     false
% 2.34/1.06  
% 2.34/1.06  ------ Preprocessing Options
% 2.34/1.06  
% 2.34/1.06  --preprocessing_flag                    true
% 2.34/1.06  --time_out_prep_mult                    0.1
% 2.34/1.06  --splitting_mode                        input
% 2.34/1.06  --splitting_grd                         true
% 2.34/1.06  --splitting_cvd                         false
% 2.34/1.06  --splitting_cvd_svl                     false
% 2.34/1.06  --splitting_nvd                         32
% 2.34/1.06  --sub_typing                            true
% 2.34/1.06  --prep_gs_sim                           true
% 2.34/1.06  --prep_unflatten                        true
% 2.34/1.06  --prep_res_sim                          true
% 2.34/1.06  --prep_upred                            true
% 2.34/1.06  --prep_sem_filter                       exhaustive
% 2.34/1.06  --prep_sem_filter_out                   false
% 2.34/1.06  --pred_elim                             true
% 2.34/1.06  --res_sim_input                         true
% 2.34/1.06  --eq_ax_congr_red                       true
% 2.34/1.06  --pure_diseq_elim                       true
% 2.34/1.06  --brand_transform                       false
% 2.34/1.06  --non_eq_to_eq                          false
% 2.34/1.06  --prep_def_merge                        true
% 2.34/1.06  --prep_def_merge_prop_impl              false
% 2.34/1.06  --prep_def_merge_mbd                    true
% 2.34/1.06  --prep_def_merge_tr_red                 false
% 2.34/1.06  --prep_def_merge_tr_cl                  false
% 2.34/1.06  --smt_preprocessing                     true
% 2.34/1.06  --smt_ac_axioms                         fast
% 2.34/1.06  --preprocessed_out                      false
% 2.34/1.06  --preprocessed_stats                    false
% 2.34/1.06  
% 2.34/1.06  ------ Abstraction refinement Options
% 2.34/1.06  
% 2.34/1.06  --abstr_ref                             []
% 2.34/1.06  --abstr_ref_prep                        false
% 2.34/1.06  --abstr_ref_until_sat                   false
% 2.34/1.06  --abstr_ref_sig_restrict                funpre
% 2.34/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/1.06  --abstr_ref_under                       []
% 2.34/1.06  
% 2.34/1.06  ------ SAT Options
% 2.34/1.06  
% 2.34/1.06  --sat_mode                              false
% 2.34/1.06  --sat_fm_restart_options                ""
% 2.34/1.06  --sat_gr_def                            false
% 2.34/1.06  --sat_epr_types                         true
% 2.34/1.06  --sat_non_cyclic_types                  false
% 2.34/1.06  --sat_finite_models                     false
% 2.34/1.06  --sat_fm_lemmas                         false
% 2.34/1.06  --sat_fm_prep                           false
% 2.34/1.06  --sat_fm_uc_incr                        true
% 2.34/1.06  --sat_out_model                         small
% 2.34/1.06  --sat_out_clauses                       false
% 2.34/1.06  
% 2.34/1.06  ------ QBF Options
% 2.34/1.06  
% 2.34/1.06  --qbf_mode                              false
% 2.34/1.06  --qbf_elim_univ                         false
% 2.34/1.06  --qbf_dom_inst                          none
% 2.34/1.06  --qbf_dom_pre_inst                      false
% 2.34/1.06  --qbf_sk_in                             false
% 2.34/1.06  --qbf_pred_elim                         true
% 2.34/1.06  --qbf_split                             512
% 2.34/1.06  
% 2.34/1.06  ------ BMC1 Options
% 2.34/1.06  
% 2.34/1.06  --bmc1_incremental                      false
% 2.34/1.06  --bmc1_axioms                           reachable_all
% 2.34/1.06  --bmc1_min_bound                        0
% 2.34/1.06  --bmc1_max_bound                        -1
% 2.34/1.06  --bmc1_max_bound_default                -1
% 2.34/1.06  --bmc1_symbol_reachability              true
% 2.34/1.06  --bmc1_property_lemmas                  false
% 2.34/1.06  --bmc1_k_induction                      false
% 2.34/1.06  --bmc1_non_equiv_states                 false
% 2.34/1.06  --bmc1_deadlock                         false
% 2.34/1.06  --bmc1_ucm                              false
% 2.34/1.06  --bmc1_add_unsat_core                   none
% 2.34/1.06  --bmc1_unsat_core_children              false
% 2.34/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/1.06  --bmc1_out_stat                         full
% 2.34/1.06  --bmc1_ground_init                      false
% 2.34/1.06  --bmc1_pre_inst_next_state              false
% 2.34/1.06  --bmc1_pre_inst_state                   false
% 2.34/1.06  --bmc1_pre_inst_reach_state             false
% 2.34/1.06  --bmc1_out_unsat_core                   false
% 2.34/1.06  --bmc1_aig_witness_out                  false
% 2.34/1.06  --bmc1_verbose                          false
% 2.34/1.06  --bmc1_dump_clauses_tptp                false
% 2.34/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.34/1.06  --bmc1_dump_file                        -
% 2.34/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.34/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.34/1.06  --bmc1_ucm_extend_mode                  1
% 2.34/1.06  --bmc1_ucm_init_mode                    2
% 2.34/1.06  --bmc1_ucm_cone_mode                    none
% 2.34/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.34/1.06  --bmc1_ucm_relax_model                  4
% 2.34/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.34/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/1.06  --bmc1_ucm_layered_model                none
% 2.34/1.06  --bmc1_ucm_max_lemma_size               10
% 2.34/1.06  
% 2.34/1.06  ------ AIG Options
% 2.34/1.06  
% 2.34/1.06  --aig_mode                              false
% 2.34/1.06  
% 2.34/1.06  ------ Instantiation Options
% 2.34/1.06  
% 2.34/1.06  --instantiation_flag                    true
% 2.34/1.06  --inst_sos_flag                         false
% 2.34/1.06  --inst_sos_phase                        true
% 2.34/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/1.06  --inst_lit_sel_side                     none
% 2.34/1.06  --inst_solver_per_active                1400
% 2.34/1.06  --inst_solver_calls_frac                1.
% 2.34/1.06  --inst_passive_queue_type               priority_queues
% 2.34/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/1.06  --inst_passive_queues_freq              [25;2]
% 2.34/1.06  --inst_dismatching                      true
% 2.34/1.06  --inst_eager_unprocessed_to_passive     true
% 2.34/1.06  --inst_prop_sim_given                   true
% 2.34/1.06  --inst_prop_sim_new                     false
% 2.34/1.06  --inst_subs_new                         false
% 2.34/1.06  --inst_eq_res_simp                      false
% 2.34/1.06  --inst_subs_given                       false
% 2.34/1.06  --inst_orphan_elimination               true
% 2.34/1.06  --inst_learning_loop_flag               true
% 2.34/1.06  --inst_learning_start                   3000
% 2.34/1.06  --inst_learning_factor                  2
% 2.34/1.06  --inst_start_prop_sim_after_learn       3
% 2.34/1.06  --inst_sel_renew                        solver
% 2.34/1.06  --inst_lit_activity_flag                true
% 2.34/1.06  --inst_restr_to_given                   false
% 2.34/1.06  --inst_activity_threshold               500
% 2.34/1.06  --inst_out_proof                        true
% 2.34/1.06  
% 2.34/1.06  ------ Resolution Options
% 2.34/1.06  
% 2.34/1.06  --resolution_flag                       false
% 2.34/1.06  --res_lit_sel                           adaptive
% 2.34/1.06  --res_lit_sel_side                      none
% 2.34/1.06  --res_ordering                          kbo
% 2.34/1.06  --res_to_prop_solver                    active
% 2.34/1.06  --res_prop_simpl_new                    false
% 2.34/1.06  --res_prop_simpl_given                  true
% 2.34/1.06  --res_passive_queue_type                priority_queues
% 2.34/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/1.06  --res_passive_queues_freq               [15;5]
% 2.34/1.06  --res_forward_subs                      full
% 2.34/1.06  --res_backward_subs                     full
% 2.34/1.06  --res_forward_subs_resolution           true
% 2.34/1.06  --res_backward_subs_resolution          true
% 2.34/1.06  --res_orphan_elimination                true
% 2.34/1.06  --res_time_limit                        2.
% 2.34/1.06  --res_out_proof                         true
% 2.34/1.06  
% 2.34/1.06  ------ Superposition Options
% 2.34/1.06  
% 2.34/1.06  --superposition_flag                    true
% 2.34/1.06  --sup_passive_queue_type                priority_queues
% 2.34/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.34/1.06  --demod_completeness_check              fast
% 2.34/1.06  --demod_use_ground                      true
% 2.34/1.06  --sup_to_prop_solver                    passive
% 2.34/1.06  --sup_prop_simpl_new                    true
% 2.34/1.06  --sup_prop_simpl_given                  true
% 2.34/1.06  --sup_fun_splitting                     false
% 2.34/1.06  --sup_smt_interval                      50000
% 2.34/1.06  
% 2.34/1.06  ------ Superposition Simplification Setup
% 2.34/1.06  
% 2.34/1.06  --sup_indices_passive                   []
% 2.34/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_full_bw                           [BwDemod]
% 2.34/1.06  --sup_immed_triv                        [TrivRules]
% 2.34/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_immed_bw_main                     []
% 2.34/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/1.06  
% 2.34/1.06  ------ Combination Options
% 2.34/1.06  
% 2.34/1.06  --comb_res_mult                         3
% 2.34/1.06  --comb_sup_mult                         2
% 2.34/1.06  --comb_inst_mult                        10
% 2.34/1.06  
% 2.34/1.06  ------ Debug Options
% 2.34/1.06  
% 2.34/1.06  --dbg_backtrace                         false
% 2.34/1.06  --dbg_dump_prop_clauses                 false
% 2.34/1.06  --dbg_dump_prop_clauses_file            -
% 2.34/1.06  --dbg_out_stat                          false
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  ------ Proving...
% 2.34/1.06  
% 2.34/1.06  
% 2.34/1.06  % SZS status Theorem for theBenchmark.p
% 2.34/1.06  
% 2.34/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/1.06  
% 2.34/1.06  fof(f16,conjecture,(
% 2.34/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f17,negated_conjecture,(
% 2.34/1.06    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.34/1.06    inference(negated_conjecture,[],[f16])).
% 2.34/1.06  
% 2.34/1.06  fof(f35,plain,(
% 2.34/1.06    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.34/1.06    inference(ennf_transformation,[],[f17])).
% 2.34/1.06  
% 2.34/1.06  fof(f36,plain,(
% 2.34/1.06    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.34/1.06    inference(flattening,[],[f35])).
% 2.34/1.06  
% 2.34/1.06  fof(f48,plain,(
% 2.34/1.06    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK5) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK5,X0,X1) & v1_funct_1(sK5))) )),
% 2.34/1.06    introduced(choice_axiom,[])).
% 2.34/1.06  
% 2.34/1.06  fof(f47,plain,(
% 2.34/1.06    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK2,sK3,sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.34/1.06    introduced(choice_axiom,[])).
% 2.34/1.06  
% 2.34/1.06  fof(f49,plain,(
% 2.34/1.06    (~r2_relset_1(sK2,sK3,sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_partfun1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.34/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f48,f47])).
% 2.34/1.06  
% 2.34/1.06  fof(f81,plain,(
% 2.34/1.06    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f1,axiom,(
% 2.34/1.06    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f18,plain,(
% 2.34/1.06    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.34/1.06    inference(unused_predicate_definition_removal,[],[f1])).
% 2.34/1.06  
% 2.34/1.06  fof(f20,plain,(
% 2.34/1.06    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.34/1.06    inference(ennf_transformation,[],[f18])).
% 2.34/1.06  
% 2.34/1.06  fof(f50,plain,(
% 2.34/1.06    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.34/1.06    inference(cnf_transformation,[],[f20])).
% 2.34/1.06  
% 2.34/1.06  fof(f12,axiom,(
% 2.34/1.06    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f28,plain,(
% 2.34/1.06    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.34/1.06    inference(ennf_transformation,[],[f12])).
% 2.34/1.06  
% 2.34/1.06  fof(f45,plain,(
% 2.34/1.06    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.34/1.06    introduced(choice_axiom,[])).
% 2.34/1.06  
% 2.34/1.06  fof(f46,plain,(
% 2.34/1.06    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.34/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f45])).
% 2.34/1.06  
% 2.34/1.06  fof(f67,plain,(
% 2.34/1.06    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.34/1.06    inference(cnf_transformation,[],[f46])).
% 2.34/1.06  
% 2.34/1.06  fof(f13,axiom,(
% 2.34/1.06    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f29,plain,(
% 2.34/1.06    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.34/1.06    inference(ennf_transformation,[],[f13])).
% 2.34/1.06  
% 2.34/1.06  fof(f30,plain,(
% 2.34/1.06    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.34/1.06    inference(flattening,[],[f29])).
% 2.34/1.06  
% 2.34/1.06  fof(f71,plain,(
% 2.34/1.06    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.34/1.06    inference(cnf_transformation,[],[f30])).
% 2.34/1.06  
% 2.34/1.06  fof(f77,plain,(
% 2.34/1.06    v1_funct_2(sK4,sK2,sK3)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f76,plain,(
% 2.34/1.06    v1_funct_1(sK4)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f78,plain,(
% 2.34/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f80,plain,(
% 2.34/1.06    v1_funct_2(sK5,sK2,sK3)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f79,plain,(
% 2.34/1.06    v1_funct_1(sK5)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f14,axiom,(
% 2.34/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f31,plain,(
% 2.34/1.06    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.34/1.06    inference(ennf_transformation,[],[f14])).
% 2.34/1.06  
% 2.34/1.06  fof(f32,plain,(
% 2.34/1.06    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.34/1.06    inference(flattening,[],[f31])).
% 2.34/1.06  
% 2.34/1.06  fof(f72,plain,(
% 2.34/1.06    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.34/1.06    inference(cnf_transformation,[],[f32])).
% 2.34/1.06  
% 2.34/1.06  fof(f82,plain,(
% 2.34/1.06    r1_partfun1(sK4,sK5)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f11,axiom,(
% 2.34/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f26,plain,(
% 2.34/1.06    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.34/1.06    inference(ennf_transformation,[],[f11])).
% 2.34/1.06  
% 2.34/1.06  fof(f27,plain,(
% 2.34/1.06    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/1.06    inference(flattening,[],[f26])).
% 2.34/1.06  
% 2.34/1.06  fof(f66,plain,(
% 2.34/1.06    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/1.06    inference(cnf_transformation,[],[f27])).
% 2.34/1.06  
% 2.34/1.06  fof(f84,plain,(
% 2.34/1.06    ~r2_relset_1(sK2,sK3,sK4,sK5)),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f83,plain,(
% 2.34/1.06    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 2.34/1.06    inference(cnf_transformation,[],[f49])).
% 2.34/1.06  
% 2.34/1.06  fof(f3,axiom,(
% 2.34/1.06    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f39,plain,(
% 2.34/1.06    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.34/1.06    inference(nnf_transformation,[],[f3])).
% 2.34/1.06  
% 2.34/1.06  fof(f40,plain,(
% 2.34/1.06    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.34/1.06    inference(flattening,[],[f39])).
% 2.34/1.06  
% 2.34/1.06  fof(f55,plain,(
% 2.34/1.06    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.34/1.06    inference(cnf_transformation,[],[f40])).
% 2.34/1.06  
% 2.34/1.06  fof(f88,plain,(
% 2.34/1.06    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.34/1.06    inference(equality_resolution,[],[f55])).
% 2.34/1.06  
% 2.34/1.06  fof(f2,axiom,(
% 2.34/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f37,plain,(
% 2.34/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/1.06    inference(nnf_transformation,[],[f2])).
% 2.34/1.06  
% 2.34/1.06  fof(f38,plain,(
% 2.34/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/1.06    inference(flattening,[],[f37])).
% 2.34/1.06  
% 2.34/1.06  fof(f53,plain,(
% 2.34/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.34/1.06    inference(cnf_transformation,[],[f38])).
% 2.34/1.06  
% 2.34/1.06  fof(f5,axiom,(
% 2.34/1.06    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f58,plain,(
% 2.34/1.06    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.34/1.06    inference(cnf_transformation,[],[f5])).
% 2.34/1.06  
% 2.34/1.06  fof(f6,axiom,(
% 2.34/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/1.06  
% 2.34/1.06  fof(f43,plain,(
% 2.34/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.34/1.06    inference(nnf_transformation,[],[f6])).
% 2.34/1.06  
% 2.34/1.06  fof(f59,plain,(
% 2.34/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/1.06    inference(cnf_transformation,[],[f43])).
% 2.34/1.06  
% 2.34/1.06  cnf(c_1150,plain,
% 2.34/1.06      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.34/1.06      theory(equality) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_2342,plain,
% 2.34/1.06      ( ~ r1_tarski(X0,sK5) | r1_tarski(X1,sK5) | X1 != X0 ),
% 2.34/1.06      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_5142,plain,
% 2.34/1.06      ( ~ r1_tarski(X0,sK5) | r1_tarski(sK4,sK5) | sK4 != X0 ),
% 2.34/1.06      inference(instantiation,[status(thm)],[c_2342]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_5144,plain,
% 2.34/1.06      ( r1_tarski(sK4,sK5)
% 2.34/1.06      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.34/1.06      | sK4 != k1_xboole_0 ),
% 2.34/1.06      inference(instantiation,[status(thm)],[c_5142]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_29,negated_conjecture,
% 2.34/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.34/1.06      inference(cnf_transformation,[],[f81]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_1688,plain,
% 2.34/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.06      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_0,plain,
% 2.34/1.06      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.34/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_19,plain,
% 2.34/1.06      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.34/1.06      inference(cnf_transformation,[],[f67]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_549,plain,
% 2.34/1.06      ( ~ v1_xboole_0(X0) | X1 != X0 | sK1(X1) != X2 | k1_xboole_0 = X1 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_550,plain,
% 2.34/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.34/1.06      inference(unflattening,[status(thm)],[c_549]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_20,plain,
% 2.34/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.06      | v1_partfun1(X0,X1)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | v1_xboole_0(X2) ),
% 2.34/1.06      inference(cnf_transformation,[],[f71]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_587,plain,
% 2.34/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.06      | v1_partfun1(X0,X1)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | X2 != X3
% 2.34/1.06      | k1_xboole_0 = X3 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_550,c_20]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_588,plain,
% 2.34/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.34/1.06      | v1_partfun1(X0,X1)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | k1_xboole_0 = X2 ),
% 2.34/1.06      inference(unflattening,[status(thm)],[c_587]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_33,negated_conjecture,
% 2.34/1.06      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.34/1.06      inference(cnf_transformation,[],[f77]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_655,plain,
% 2.34/1.06      ( v1_partfun1(X0,X1)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | sK4 != X0
% 2.34/1.06      | sK3 != X2
% 2.34/1.06      | sK2 != X1
% 2.34/1.06      | k1_xboole_0 = X2 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_588,c_33]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_656,plain,
% 2.34/1.06      ( v1_partfun1(sK4,sK2)
% 2.34/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.06      | ~ v1_funct_1(sK4)
% 2.34/1.06      | k1_xboole_0 = sK3 ),
% 2.34/1.06      inference(unflattening,[status(thm)],[c_655]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_34,negated_conjecture,
% 2.34/1.06      ( v1_funct_1(sK4) ),
% 2.34/1.06      inference(cnf_transformation,[],[f76]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_32,negated_conjecture,
% 2.34/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.34/1.06      inference(cnf_transformation,[],[f78]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_658,plain,
% 2.34/1.06      ( v1_partfun1(sK4,sK2) | k1_xboole_0 = sK3 ),
% 2.34/1.06      inference(global_propositional_subsumption,
% 2.34/1.06                [status(thm)],
% 2.34/1.06                [c_656,c_34,c_32]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_1682,plain,
% 2.34/1.06      ( k1_xboole_0 = sK3 | v1_partfun1(sK4,sK2) = iProver_top ),
% 2.34/1.06      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_30,negated_conjecture,
% 2.34/1.06      ( v1_funct_2(sK5,sK2,sK3) ),
% 2.34/1.06      inference(cnf_transformation,[],[f80]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_641,plain,
% 2.34/1.06      ( v1_partfun1(X0,X1)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | sK5 != X0
% 2.34/1.06      | sK3 != X2
% 2.34/1.06      | sK2 != X1
% 2.34/1.06      | k1_xboole_0 = X2 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_588,c_30]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_642,plain,
% 2.34/1.06      ( v1_partfun1(sK5,sK2)
% 2.34/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.06      | ~ v1_funct_1(sK5)
% 2.34/1.06      | k1_xboole_0 = sK3 ),
% 2.34/1.06      inference(unflattening,[status(thm)],[c_641]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_31,negated_conjecture,
% 2.34/1.06      ( v1_funct_1(sK5) ),
% 2.34/1.06      inference(cnf_transformation,[],[f79]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_644,plain,
% 2.34/1.06      ( v1_partfun1(sK5,sK2) | k1_xboole_0 = sK3 ),
% 2.34/1.06      inference(global_propositional_subsumption,
% 2.34/1.06                [status(thm)],
% 2.34/1.06                [c_642,c_31,c_29]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_1683,plain,
% 2.34/1.06      ( k1_xboole_0 = sK3 | v1_partfun1(sK5,sK2) = iProver_top ),
% 2.34/1.06      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_22,plain,
% 2.34/1.06      ( ~ r1_partfun1(X0,X1)
% 2.34/1.06      | ~ v1_partfun1(X1,X2)
% 2.34/1.06      | ~ v1_partfun1(X0,X2)
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.34/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | ~ v1_funct_1(X1)
% 2.34/1.06      | X1 = X0 ),
% 2.34/1.06      inference(cnf_transformation,[],[f72]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_28,negated_conjecture,
% 2.34/1.06      ( r1_partfun1(sK4,sK5) ),
% 2.34/1.06      inference(cnf_transformation,[],[f82]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_456,plain,
% 2.34/1.06      ( ~ v1_partfun1(X0,X1)
% 2.34/1.06      | ~ v1_partfun1(X2,X1)
% 2.34/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.34/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.34/1.06      | ~ v1_funct_1(X2)
% 2.34/1.06      | ~ v1_funct_1(X0)
% 2.34/1.06      | X0 = X2
% 2.34/1.06      | sK5 != X0
% 2.34/1.06      | sK4 != X2 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_457,plain,
% 2.34/1.06      ( ~ v1_partfun1(sK5,X0)
% 2.34/1.06      | ~ v1_partfun1(sK4,X0)
% 2.34/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.06      | ~ v1_funct_1(sK5)
% 2.34/1.06      | ~ v1_funct_1(sK4)
% 2.34/1.06      | sK5 = sK4 ),
% 2.34/1.06      inference(unflattening,[status(thm)],[c_456]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_461,plain,
% 2.34/1.06      ( ~ v1_partfun1(sK5,X0)
% 2.34/1.06      | ~ v1_partfun1(sK4,X0)
% 2.34/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.06      | sK5 = sK4 ),
% 2.34/1.06      inference(global_propositional_subsumption,
% 2.34/1.06                [status(thm)],
% 2.34/1.06                [c_457,c_34,c_31]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_1684,plain,
% 2.34/1.06      ( sK5 = sK4
% 2.34/1.06      | v1_partfun1(sK5,X0) != iProver_top
% 2.34/1.06      | v1_partfun1(sK4,X0) != iProver_top
% 2.34/1.06      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.34/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.34/1.06      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_2206,plain,
% 2.34/1.06      ( sK5 = sK4
% 2.34/1.06      | v1_partfun1(sK5,sK2) != iProver_top
% 2.34/1.06      | v1_partfun1(sK4,sK2) != iProver_top
% 2.34/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.34/1.06      inference(superposition,[status(thm)],[c_1688,c_1684]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_37,plain,
% 2.34/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_2375,plain,
% 2.34/1.06      ( v1_partfun1(sK4,sK2) != iProver_top
% 2.34/1.06      | v1_partfun1(sK5,sK2) != iProver_top
% 2.34/1.06      | sK5 = sK4 ),
% 2.34/1.06      inference(global_propositional_subsumption,
% 2.34/1.06                [status(thm)],
% 2.34/1.06                [c_2206,c_37]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_2376,plain,
% 2.34/1.06      ( sK5 = sK4
% 2.34/1.06      | v1_partfun1(sK5,sK2) != iProver_top
% 2.34/1.06      | v1_partfun1(sK4,sK2) != iProver_top ),
% 2.34/1.06      inference(renaming,[status(thm)],[c_2375]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_2521,plain,
% 2.34/1.06      ( sK5 = sK4
% 2.34/1.06      | sK3 = k1_xboole_0
% 2.34/1.06      | v1_partfun1(sK4,sK2) != iProver_top ),
% 2.34/1.06      inference(superposition,[status(thm)],[c_1683,c_2376]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_3461,plain,
% 2.34/1.06      ( sK5 = sK4 | sK3 = k1_xboole_0 ),
% 2.34/1.06      inference(superposition,[status(thm)],[c_1682,c_2521]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_16,plain,
% 2.34/1.06      ( r2_relset_1(X0,X1,X2,X2)
% 2.34/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.34/1.06      inference(cnf_transformation,[],[f66]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_26,negated_conjecture,
% 2.34/1.06      ( ~ r2_relset_1(sK2,sK3,sK4,sK5) ),
% 2.34/1.06      inference(cnf_transformation,[],[f84]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_388,plain,
% 2.34/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/1.06      | sK5 != X0
% 2.34/1.06      | sK4 != X0
% 2.34/1.06      | sK3 != X2
% 2.34/1.06      | sK2 != X1 ),
% 2.34/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.34/1.06  
% 2.34/1.06  cnf(c_389,plain,
% 2.34/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.07      | sK4 != sK5 ),
% 2.34/1.07      inference(unflattening,[status(thm)],[c_388]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_393,plain,
% 2.34/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.34/1.07      | sK4 != sK5 ),
% 2.34/1.07      inference(global_propositional_subsumption,
% 2.34/1.07                [status(thm)],
% 2.34/1.07                [c_389,c_29]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_1686,plain,
% 2.34/1.07      ( sK4 != sK5
% 2.34/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4342,plain,
% 2.34/1.07      ( sK3 = k1_xboole_0
% 2.34/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.34/1.07      inference(superposition,[status(thm)],[c_3461,c_1686]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4410,plain,
% 2.34/1.07      ( sK3 = k1_xboole_0 ),
% 2.34/1.07      inference(superposition,[status(thm)],[c_1688,c_4342]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4585,plain,
% 2.34/1.07      ( sK5 != sK4
% 2.34/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4410,c_1686]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_27,negated_conjecture,
% 2.34/1.07      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 2.34/1.07      inference(cnf_transformation,[],[f83]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4588,plain,
% 2.34/1.07      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4410,c_27]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4589,plain,
% 2.34/1.07      ( sK2 = k1_xboole_0 ),
% 2.34/1.07      inference(equality_resolution_simp,[status(thm)],[c_4588]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4600,plain,
% 2.34/1.07      ( sK5 != sK4
% 2.34/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.34/1.07      inference(light_normalisation,[status(thm)],[c_4585,c_4589]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_5,plain,
% 2.34/1.07      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.34/1.07      inference(cnf_transformation,[],[f88]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4603,plain,
% 2.34/1.07      ( sK5 != sK4
% 2.34/1.07      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4600,c_5]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4617,plain,
% 2.34/1.07      ( sK5 != sK4
% 2.34/1.07      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_4603]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4586,plain,
% 2.34/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4410,c_1688]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4596,plain,
% 2.34/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.34/1.07      inference(light_normalisation,[status(thm)],[c_4586,c_4589]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4598,plain,
% 2.34/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4596,c_5]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_1687,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4587,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4410,c_1687]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4592,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.34/1.07      inference(light_normalisation,[status(thm)],[c_4587,c_4589]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4594,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.34/1.07      inference(demodulation,[status(thm)],[c_4592,c_5]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_1,plain,
% 2.34/1.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.34/1.07      inference(cnf_transformation,[],[f53]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2014,plain,
% 2.34/1.07      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_4247,plain,
% 2.34/1.07      ( ~ r1_tarski(sK5,sK4) | ~ r1_tarski(sK4,sK5) | sK5 = sK4 ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2014]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_8,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.34/1.07      inference(cnf_transformation,[],[f58]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2935,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_8]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2938,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2935]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2884,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_8]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2885,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2884]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2682,plain,
% 2.34/1.07      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2683,plain,
% 2.34/1.07      ( sK4 = X0
% 2.34/1.07      | r1_tarski(X0,sK4) != iProver_top
% 2.34/1.07      | r1_tarski(sK4,X0) != iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2682]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2685,plain,
% 2.34/1.07      ( sK4 = k1_xboole_0
% 2.34/1.07      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2683]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_10,plain,
% 2.34/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/1.07      inference(cnf_transformation,[],[f59]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2639,plain,
% 2.34/1.07      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_10]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2640,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 2.34/1.07      | r1_tarski(sK4,X0) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2639]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2642,plain,
% 2.34/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.34/1.07      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2640]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2580,plain,
% 2.34/1.07      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_10]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2581,plain,
% 2.34/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 2.34/1.07      | r1_tarski(sK5,X0) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2583,plain,
% 2.34/1.07      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.34/1.07      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2581]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2336,plain,
% 2.34/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5)) | r1_tarski(X0,sK5) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_10]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2337,plain,
% 2.34/1.07      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 2.34/1.07      | r1_tarski(X0,sK5) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2339,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5)) != iProver_top
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2337]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2338,plain,
% 2.34/1.07      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5))
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK5) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2336]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2312,plain,
% 2.34/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_10]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2313,plain,
% 2.34/1.07      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.34/1.07      | r1_tarski(X0,sK4) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2312]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2315,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2313]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2314,plain,
% 2.34/1.07      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4))
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK4) ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2312]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2015,plain,
% 2.34/1.07      ( sK5 = X0
% 2.34/1.07      | r1_tarski(X0,sK5) != iProver_top
% 2.34/1.07      | r1_tarski(sK5,X0) != iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2017,plain,
% 2.34/1.07      ( sK5 = k1_xboole_0
% 2.34/1.07      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.34/1.07      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2009,plain,
% 2.34/1.07      ( ~ r1_tarski(X0,sK4) | r1_tarski(sK5,sK4) | sK5 != X0 ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_2011,plain,
% 2.34/1.07      ( r1_tarski(sK5,sK4)
% 2.34/1.07      | ~ r1_tarski(k1_xboole_0,sK4)
% 2.34/1.07      | sK5 != k1_xboole_0 ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_2009]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_88,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.34/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(c_90,plain,
% 2.34/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.34/1.07      inference(instantiation,[status(thm)],[c_88]) ).
% 2.34/1.07  
% 2.34/1.07  cnf(contradiction,plain,
% 2.34/1.07      ( $false ),
% 2.34/1.07      inference(minisat,
% 2.34/1.07                [status(thm)],
% 2.34/1.07                [c_5144,c_4617,c_4598,c_4594,c_4247,c_2938,c_2935,c_2885,
% 2.34/1.07                 c_2884,c_2685,c_2642,c_2583,c_2339,c_2338,c_2315,c_2314,
% 2.34/1.07                 c_2017,c_2011,c_90]) ).
% 2.34/1.07  
% 2.34/1.07  
% 2.34/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.07  
% 2.34/1.07  ------                               Statistics
% 2.34/1.07  
% 2.34/1.07  ------ General
% 2.34/1.07  
% 2.34/1.07  abstr_ref_over_cycles:                  0
% 2.34/1.07  abstr_ref_under_cycles:                 0
% 2.34/1.07  gc_basic_clause_elim:                   0
% 2.34/1.07  forced_gc_time:                         0
% 2.34/1.07  parsing_time:                           0.013
% 2.34/1.07  unif_index_cands_time:                  0.
% 2.34/1.07  unif_index_add_time:                    0.
% 2.34/1.07  orderings_time:                         0.
% 2.34/1.07  out_proof_time:                         0.01
% 2.34/1.07  total_time:                             0.178
% 2.34/1.07  num_of_symbols:                         56
% 2.34/1.07  num_of_terms:                           4351
% 2.34/1.07  
% 2.34/1.07  ------ Preprocessing
% 2.34/1.07  
% 2.34/1.07  num_of_splits:                          2
% 2.34/1.07  num_of_split_atoms:                     2
% 2.34/1.07  num_of_reused_defs:                     0
% 2.34/1.07  num_eq_ax_congr_red:                    20
% 2.34/1.07  num_of_sem_filtered_clauses:            1
% 2.34/1.07  num_of_subtypes:                        0
% 2.34/1.07  monotx_restored_types:                  0
% 2.34/1.07  sat_num_of_epr_types:                   0
% 2.34/1.07  sat_num_of_non_cyclic_types:            0
% 2.34/1.07  sat_guarded_non_collapsed_types:        0
% 2.34/1.07  num_pure_diseq_elim:                    0
% 2.34/1.07  simp_replaced_by:                       0
% 2.34/1.07  res_preprocessed:                       134
% 2.34/1.07  prep_upred:                             0
% 2.34/1.07  prep_unflattend:                        36
% 2.34/1.07  smt_new_axioms:                         0
% 2.34/1.07  pred_elim_cands:                        4
% 2.34/1.07  pred_elim:                              7
% 2.34/1.07  pred_elim_cl:                           7
% 2.34/1.07  pred_elim_cycles:                       12
% 2.34/1.07  merged_defs:                            8
% 2.34/1.07  merged_defs_ncl:                        0
% 2.34/1.07  bin_hyper_res:                          9
% 2.34/1.07  prep_cycles:                            4
% 2.34/1.07  pred_elim_time:                         0.015
% 2.34/1.07  splitting_time:                         0.
% 2.34/1.07  sem_filter_time:                        0.
% 2.34/1.07  monotx_time:                            0.
% 2.34/1.07  subtype_inf_time:                       0.
% 2.34/1.07  
% 2.34/1.07  ------ Problem properties
% 2.34/1.07  
% 2.34/1.07  clauses:                                27
% 2.34/1.07  conjectures:                            3
% 2.34/1.07  epr:                                    5
% 2.34/1.07  horn:                                   21
% 2.34/1.07  ground:                                 7
% 2.34/1.07  unary:                                  7
% 2.34/1.07  binary:                                 10
% 2.34/1.07  lits:                                   59
% 2.34/1.07  lits_eq:                                19
% 2.34/1.07  fd_pure:                                0
% 2.34/1.07  fd_pseudo:                              0
% 2.34/1.07  fd_cond:                                6
% 2.34/1.07  fd_pseudo_cond:                         1
% 2.34/1.07  ac_symbols:                             0
% 2.34/1.07  
% 2.34/1.07  ------ Propositional Solver
% 2.34/1.07  
% 2.34/1.07  prop_solver_calls:                      27
% 2.34/1.07  prop_fast_solver_calls:                 854
% 2.34/1.07  smt_solver_calls:                       0
% 2.34/1.07  smt_fast_solver_calls:                  0
% 2.34/1.07  prop_num_of_clauses:                    1840
% 2.34/1.07  prop_preprocess_simplified:             6051
% 2.34/1.07  prop_fo_subsumed:                       14
% 2.34/1.07  prop_solver_time:                       0.
% 2.34/1.07  smt_solver_time:                        0.
% 2.34/1.07  smt_fast_solver_time:                   0.
% 2.34/1.07  prop_fast_solver_time:                  0.
% 2.34/1.07  prop_unsat_core_time:                   0.
% 2.34/1.07  
% 2.34/1.07  ------ QBF
% 2.34/1.07  
% 2.34/1.07  qbf_q_res:                              0
% 2.34/1.07  qbf_num_tautologies:                    0
% 2.34/1.07  qbf_prep_cycles:                        0
% 2.34/1.07  
% 2.34/1.07  ------ BMC1
% 2.34/1.07  
% 2.34/1.07  bmc1_current_bound:                     -1
% 2.34/1.07  bmc1_last_solved_bound:                 -1
% 2.34/1.07  bmc1_unsat_core_size:                   -1
% 2.34/1.07  bmc1_unsat_core_parents_size:           -1
% 2.34/1.07  bmc1_merge_next_fun:                    0
% 2.34/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.07  
% 2.34/1.07  ------ Instantiation
% 2.34/1.07  
% 2.34/1.07  inst_num_of_clauses:                    551
% 2.34/1.07  inst_num_in_passive:                    124
% 2.34/1.07  inst_num_in_active:                     206
% 2.34/1.07  inst_num_in_unprocessed:                220
% 2.34/1.07  inst_num_of_loops:                      251
% 2.34/1.07  inst_num_of_learning_restarts:          0
% 2.34/1.07  inst_num_moves_active_passive:          42
% 2.34/1.07  inst_lit_activity:                      0
% 2.34/1.07  inst_lit_activity_moves:                0
% 2.34/1.07  inst_num_tautologies:                   0
% 2.34/1.07  inst_num_prop_implied:                  0
% 2.34/1.07  inst_num_existing_simplified:           0
% 2.34/1.07  inst_num_eq_res_simplified:             0
% 2.34/1.07  inst_num_child_elim:                    0
% 2.34/1.07  inst_num_of_dismatching_blockings:      142
% 2.34/1.07  inst_num_of_non_proper_insts:           444
% 2.34/1.07  inst_num_of_duplicates:                 0
% 2.34/1.07  inst_inst_num_from_inst_to_res:         0
% 2.34/1.07  inst_dismatching_checking_time:         0.
% 2.34/1.07  
% 2.34/1.07  ------ Resolution
% 2.34/1.07  
% 2.34/1.07  res_num_of_clauses:                     0
% 2.34/1.07  res_num_in_passive:                     0
% 2.34/1.07  res_num_in_active:                      0
% 2.34/1.07  res_num_of_loops:                       138
% 2.34/1.07  res_forward_subset_subsumed:            50
% 2.34/1.07  res_backward_subset_subsumed:           4
% 2.34/1.07  res_forward_subsumed:                   0
% 2.34/1.07  res_backward_subsumed:                  0
% 2.34/1.07  res_forward_subsumption_resolution:     0
% 2.34/1.07  res_backward_subsumption_resolution:    0
% 2.34/1.07  res_clause_to_clause_subsumption:       275
% 2.34/1.07  res_orphan_elimination:                 0
% 2.34/1.07  res_tautology_del:                      45
% 2.34/1.07  res_num_eq_res_simplified:              0
% 2.34/1.07  res_num_sel_changes:                    0
% 2.34/1.07  res_moves_from_active_to_pass:          0
% 2.34/1.07  
% 2.34/1.07  ------ Superposition
% 2.34/1.07  
% 2.34/1.07  sup_time_total:                         0.
% 2.34/1.07  sup_time_generating:                    0.
% 2.34/1.07  sup_time_sim_full:                      0.
% 2.34/1.07  sup_time_sim_immed:                     0.
% 2.34/1.07  
% 2.34/1.07  sup_num_of_clauses:                     61
% 2.34/1.07  sup_num_in_active:                      37
% 2.34/1.07  sup_num_in_passive:                     24
% 2.34/1.07  sup_num_of_loops:                       50
% 2.34/1.07  sup_fw_superposition:                   47
% 2.34/1.07  sup_bw_superposition:                   28
% 2.34/1.07  sup_immediate_simplified:               31
% 2.34/1.07  sup_given_eliminated:                   0
% 2.34/1.07  comparisons_done:                       0
% 2.34/1.07  comparisons_avoided:                    3
% 2.34/1.07  
% 2.34/1.07  ------ Simplifications
% 2.34/1.07  
% 2.34/1.07  
% 2.34/1.07  sim_fw_subset_subsumed:                 9
% 2.34/1.07  sim_bw_subset_subsumed:                 14
% 2.34/1.07  sim_fw_subsumed:                        1
% 2.34/1.07  sim_bw_subsumed:                        4
% 2.34/1.07  sim_fw_subsumption_res:                 0
% 2.34/1.07  sim_bw_subsumption_res:                 0
% 2.34/1.07  sim_tautology_del:                      3
% 2.34/1.07  sim_eq_tautology_del:                   3
% 2.34/1.07  sim_eq_res_simp:                        1
% 2.34/1.07  sim_fw_demodulated:                     5
% 2.34/1.07  sim_bw_demodulated:                     9
% 2.34/1.07  sim_light_normalised:                   9
% 2.34/1.07  sim_joinable_taut:                      0
% 2.34/1.07  sim_joinable_simp:                      0
% 2.34/1.07  sim_ac_normalised:                      0
% 2.34/1.07  sim_smt_subsumption:                    0
% 2.34/1.07  
%------------------------------------------------------------------------------
