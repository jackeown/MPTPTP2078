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
% DateTime   : Thu Dec  3 12:08:34 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  119 (1057 expanded)
%              Number of clauses        :   73 ( 313 expanded)
%              Number of leaves         :   14 ( 277 expanded)
%              Depth                    :   18
%              Number of atoms          :  404 (7669 expanded)
%              Number of equality atoms :  122 (1675 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK4,X0,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & r1_partfun1(sK3,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_partfun1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f32,f31])).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_720,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_715,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_713,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1127,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_713])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_291,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_292,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_294,plain,
    ( v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_22,c_20])).

cnf(c_707,plain,
    ( v1_partfun1(sK3,sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_277,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_278,plain,
    ( v1_partfun1(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_280,plain,
    ( v1_partfun1(sK4,sK1)
    | v1_xboole_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_19,c_17])).

cnf(c_282,plain,
    ( v1_partfun1(sK4,sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_296,plain,
    ( v1_partfun1(sK3,sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_417,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_905,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_712,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_244,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK4 != X0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_245,plain,
    ( ~ v1_partfun1(sK4,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | sK4 = sK3 ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_249,plain,
    ( ~ v1_partfun1(sK4,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_245,c_22,c_19])).

cnf(c_709,plain,
    ( sK4 = sK3
    | v1_partfun1(sK4,X0) != iProver_top
    | v1_partfun1(sK3,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_923,plain,
    ( sK4 = sK3
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_709])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_926,plain,
    ( v1_partfun1(sK3,sK1) != iProver_top
    | v1_partfun1(sK4,sK1) != iProver_top
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_25])).

cnf(c_927,plain,
    ( sK4 = sK3
    | v1_partfun1(sK4,sK1) != iProver_top
    | v1_partfun1(sK3,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_926])).

cnf(c_418,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_841,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_946,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_17])).

cnf(c_972,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_973,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1000,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_282,c_296,c_905,c_927,c_946,c_972,c_973])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1350,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1348])).

cnf(c_1349,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1354,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1349])).

cnf(c_1357,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1127,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1350,c_1354])).

cnf(c_1364,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_1357])).

cnf(c_711,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1015,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_713])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1182,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,sK2))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1183,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_1185,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_1225,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1185])).

cnf(c_1232,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_1225])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_718,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1421,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_718])).

cnf(c_1615,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1364,c_1421])).

cnf(c_1014,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_713])).

cnf(c_1213,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1185])).

cnf(c_1220,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_1213])).

cnf(c_1420,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_718])).

cnf(c_1603,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1364,c_1420])).

cnf(c_1535,plain,
    ( sK4 != k1_xboole_0
    | sK3 = sK4
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1615,c_1603,c_1535,c_973,c_972])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.47/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.47/0.98  
% 1.47/0.98  ------  iProver source info
% 1.47/0.98  
% 1.47/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.47/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.47/0.98  git: non_committed_changes: false
% 1.47/0.98  git: last_make_outside_of_git: false
% 1.47/0.98  
% 1.47/0.98  ------ 
% 1.47/0.98  
% 1.47/0.98  ------ Input Options
% 1.47/0.98  
% 1.47/0.98  --out_options                           all
% 1.47/0.98  --tptp_safe_out                         true
% 1.47/0.98  --problem_path                          ""
% 1.47/0.98  --include_path                          ""
% 1.47/0.98  --clausifier                            res/vclausify_rel
% 1.47/0.98  --clausifier_options                    --mode clausify
% 1.47/0.98  --stdin                                 false
% 1.47/0.98  --stats_out                             all
% 1.47/0.98  
% 1.47/0.98  ------ General Options
% 1.47/0.98  
% 1.47/0.98  --fof                                   false
% 1.47/0.98  --time_out_real                         305.
% 1.47/0.98  --time_out_virtual                      -1.
% 1.47/0.98  --symbol_type_check                     false
% 1.47/0.98  --clausify_out                          false
% 1.47/0.98  --sig_cnt_out                           false
% 1.47/0.98  --trig_cnt_out                          false
% 1.47/0.98  --trig_cnt_out_tolerance                1.
% 1.47/0.98  --trig_cnt_out_sk_spl                   false
% 1.47/0.98  --abstr_cl_out                          false
% 1.47/0.98  
% 1.47/0.98  ------ Global Options
% 1.47/0.98  
% 1.47/0.98  --schedule                              default
% 1.47/0.98  --add_important_lit                     false
% 1.47/0.98  --prop_solver_per_cl                    1000
% 1.47/0.98  --min_unsat_core                        false
% 1.47/0.98  --soft_assumptions                      false
% 1.47/0.98  --soft_lemma_size                       3
% 1.47/0.98  --prop_impl_unit_size                   0
% 1.47/0.98  --prop_impl_unit                        []
% 1.47/0.98  --share_sel_clauses                     true
% 1.47/0.98  --reset_solvers                         false
% 1.47/0.98  --bc_imp_inh                            [conj_cone]
% 1.47/0.98  --conj_cone_tolerance                   3.
% 1.47/0.98  --extra_neg_conj                        none
% 1.47/0.98  --large_theory_mode                     true
% 1.47/0.98  --prolific_symb_bound                   200
% 1.47/0.98  --lt_threshold                          2000
% 1.47/0.98  --clause_weak_htbl                      true
% 1.47/0.98  --gc_record_bc_elim                     false
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing Options
% 1.47/0.98  
% 1.47/0.98  --preprocessing_flag                    true
% 1.47/0.98  --time_out_prep_mult                    0.1
% 1.47/0.98  --splitting_mode                        input
% 1.47/0.98  --splitting_grd                         true
% 1.47/0.98  --splitting_cvd                         false
% 1.47/0.98  --splitting_cvd_svl                     false
% 1.47/0.98  --splitting_nvd                         32
% 1.47/0.98  --sub_typing                            true
% 1.47/0.98  --prep_gs_sim                           true
% 1.47/0.98  --prep_unflatten                        true
% 1.47/0.98  --prep_res_sim                          true
% 1.47/0.98  --prep_upred                            true
% 1.47/0.98  --prep_sem_filter                       exhaustive
% 1.47/0.98  --prep_sem_filter_out                   false
% 1.47/0.98  --pred_elim                             true
% 1.47/0.98  --res_sim_input                         true
% 1.47/0.98  --eq_ax_congr_red                       true
% 1.47/0.98  --pure_diseq_elim                       true
% 1.47/0.98  --brand_transform                       false
% 1.47/0.98  --non_eq_to_eq                          false
% 1.47/0.98  --prep_def_merge                        true
% 1.47/0.98  --prep_def_merge_prop_impl              false
% 1.47/0.98  --prep_def_merge_mbd                    true
% 1.47/0.98  --prep_def_merge_tr_red                 false
% 1.47/0.98  --prep_def_merge_tr_cl                  false
% 1.47/0.98  --smt_preprocessing                     true
% 1.47/0.98  --smt_ac_axioms                         fast
% 1.47/0.98  --preprocessed_out                      false
% 1.47/0.98  --preprocessed_stats                    false
% 1.47/0.98  
% 1.47/0.98  ------ Abstraction refinement Options
% 1.47/0.98  
% 1.47/0.98  --abstr_ref                             []
% 1.47/0.98  --abstr_ref_prep                        false
% 1.47/0.98  --abstr_ref_until_sat                   false
% 1.47/0.98  --abstr_ref_sig_restrict                funpre
% 1.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.47/0.98  --abstr_ref_under                       []
% 1.47/0.98  
% 1.47/0.98  ------ SAT Options
% 1.47/0.98  
% 1.47/0.98  --sat_mode                              false
% 1.47/0.98  --sat_fm_restart_options                ""
% 1.47/0.98  --sat_gr_def                            false
% 1.47/0.98  --sat_epr_types                         true
% 1.47/0.98  --sat_non_cyclic_types                  false
% 1.47/0.98  --sat_finite_models                     false
% 1.47/0.98  --sat_fm_lemmas                         false
% 1.47/0.98  --sat_fm_prep                           false
% 1.47/0.98  --sat_fm_uc_incr                        true
% 1.47/0.98  --sat_out_model                         small
% 1.47/0.98  --sat_out_clauses                       false
% 1.47/0.98  
% 1.47/0.98  ------ QBF Options
% 1.47/0.98  
% 1.47/0.98  --qbf_mode                              false
% 1.47/0.98  --qbf_elim_univ                         false
% 1.47/0.98  --qbf_dom_inst                          none
% 1.47/0.98  --qbf_dom_pre_inst                      false
% 1.47/0.98  --qbf_sk_in                             false
% 1.47/0.98  --qbf_pred_elim                         true
% 1.47/0.98  --qbf_split                             512
% 1.47/0.98  
% 1.47/0.98  ------ BMC1 Options
% 1.47/0.98  
% 1.47/0.98  --bmc1_incremental                      false
% 1.47/0.98  --bmc1_axioms                           reachable_all
% 1.47/0.98  --bmc1_min_bound                        0
% 1.47/0.98  --bmc1_max_bound                        -1
% 1.47/0.98  --bmc1_max_bound_default                -1
% 1.47/0.98  --bmc1_symbol_reachability              true
% 1.47/0.98  --bmc1_property_lemmas                  false
% 1.47/0.98  --bmc1_k_induction                      false
% 1.47/0.98  --bmc1_non_equiv_states                 false
% 1.47/0.98  --bmc1_deadlock                         false
% 1.47/0.98  --bmc1_ucm                              false
% 1.47/0.98  --bmc1_add_unsat_core                   none
% 1.47/0.98  --bmc1_unsat_core_children              false
% 1.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.47/0.98  --bmc1_out_stat                         full
% 1.47/0.98  --bmc1_ground_init                      false
% 1.47/0.98  --bmc1_pre_inst_next_state              false
% 1.47/0.98  --bmc1_pre_inst_state                   false
% 1.47/0.98  --bmc1_pre_inst_reach_state             false
% 1.47/0.98  --bmc1_out_unsat_core                   false
% 1.47/0.98  --bmc1_aig_witness_out                  false
% 1.47/0.98  --bmc1_verbose                          false
% 1.47/0.98  --bmc1_dump_clauses_tptp                false
% 1.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.47/0.98  --bmc1_dump_file                        -
% 1.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.47/0.98  --bmc1_ucm_extend_mode                  1
% 1.47/0.98  --bmc1_ucm_init_mode                    2
% 1.47/0.98  --bmc1_ucm_cone_mode                    none
% 1.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.47/0.98  --bmc1_ucm_relax_model                  4
% 1.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.47/0.98  --bmc1_ucm_layered_model                none
% 1.47/0.98  --bmc1_ucm_max_lemma_size               10
% 1.47/0.98  
% 1.47/0.98  ------ AIG Options
% 1.47/0.98  
% 1.47/0.98  --aig_mode                              false
% 1.47/0.98  
% 1.47/0.98  ------ Instantiation Options
% 1.47/0.98  
% 1.47/0.98  --instantiation_flag                    true
% 1.47/0.98  --inst_sos_flag                         false
% 1.47/0.98  --inst_sos_phase                        true
% 1.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.47/0.98  --inst_lit_sel_side                     num_symb
% 1.47/0.98  --inst_solver_per_active                1400
% 1.47/0.98  --inst_solver_calls_frac                1.
% 1.47/0.98  --inst_passive_queue_type               priority_queues
% 1.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.47/0.98  --inst_passive_queues_freq              [25;2]
% 1.47/0.98  --inst_dismatching                      true
% 1.47/0.98  --inst_eager_unprocessed_to_passive     true
% 1.47/0.98  --inst_prop_sim_given                   true
% 1.47/0.98  --inst_prop_sim_new                     false
% 1.47/0.98  --inst_subs_new                         false
% 1.47/0.98  --inst_eq_res_simp                      false
% 1.47/0.98  --inst_subs_given                       false
% 1.47/0.98  --inst_orphan_elimination               true
% 1.47/0.98  --inst_learning_loop_flag               true
% 1.47/0.98  --inst_learning_start                   3000
% 1.47/0.98  --inst_learning_factor                  2
% 1.47/0.98  --inst_start_prop_sim_after_learn       3
% 1.47/0.98  --inst_sel_renew                        solver
% 1.47/0.98  --inst_lit_activity_flag                true
% 1.47/0.98  --inst_restr_to_given                   false
% 1.47/0.98  --inst_activity_threshold               500
% 1.47/0.98  --inst_out_proof                        true
% 1.47/0.98  
% 1.47/0.98  ------ Resolution Options
% 1.47/0.98  
% 1.47/0.98  --resolution_flag                       true
% 1.47/0.98  --res_lit_sel                           adaptive
% 1.47/0.98  --res_lit_sel_side                      none
% 1.47/0.98  --res_ordering                          kbo
% 1.47/0.98  --res_to_prop_solver                    active
% 1.47/0.98  --res_prop_simpl_new                    false
% 1.47/0.98  --res_prop_simpl_given                  true
% 1.47/0.98  --res_passive_queue_type                priority_queues
% 1.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.47/0.98  --res_passive_queues_freq               [15;5]
% 1.47/0.98  --res_forward_subs                      full
% 1.47/0.98  --res_backward_subs                     full
% 1.47/0.98  --res_forward_subs_resolution           true
% 1.47/0.98  --res_backward_subs_resolution          true
% 1.47/0.98  --res_orphan_elimination                true
% 1.47/0.98  --res_time_limit                        2.
% 1.47/0.98  --res_out_proof                         true
% 1.47/0.98  
% 1.47/0.98  ------ Superposition Options
% 1.47/0.98  
% 1.47/0.98  --superposition_flag                    true
% 1.47/0.98  --sup_passive_queue_type                priority_queues
% 1.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.47/0.98  --demod_completeness_check              fast
% 1.47/0.98  --demod_use_ground                      true
% 1.47/0.98  --sup_to_prop_solver                    passive
% 1.47/0.98  --sup_prop_simpl_new                    true
% 1.47/0.98  --sup_prop_simpl_given                  true
% 1.47/0.98  --sup_fun_splitting                     false
% 1.47/0.98  --sup_smt_interval                      50000
% 1.47/0.98  
% 1.47/0.98  ------ Superposition Simplification Setup
% 1.47/0.98  
% 1.47/0.98  --sup_indices_passive                   []
% 1.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_full_bw                           [BwDemod]
% 1.47/0.98  --sup_immed_triv                        [TrivRules]
% 1.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_immed_bw_main                     []
% 1.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/0.98  
% 1.47/0.98  ------ Combination Options
% 1.47/0.98  
% 1.47/0.98  --comb_res_mult                         3
% 1.47/0.98  --comb_sup_mult                         2
% 1.47/0.98  --comb_inst_mult                        10
% 1.47/0.98  
% 1.47/0.98  ------ Debug Options
% 1.47/0.98  
% 1.47/0.98  --dbg_backtrace                         false
% 1.47/0.98  --dbg_dump_prop_clauses                 false
% 1.47/0.98  --dbg_dump_prop_clauses_file            -
% 1.47/0.98  --dbg_out_stat                          false
% 1.47/0.98  ------ Parsing...
% 1.47/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.47/0.98  ------ Proving...
% 1.47/0.98  ------ Problem Properties 
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  clauses                                 16
% 1.47/0.98  conjectures                             3
% 1.47/0.98  EPR                                     6
% 1.47/0.98  Horn                                    13
% 1.47/0.98  unary                                   4
% 1.47/0.98  binary                                  7
% 1.47/0.98  lits                                    35
% 1.47/0.98  lits eq                                 5
% 1.47/0.98  fd_pure                                 0
% 1.47/0.98  fd_pseudo                               0
% 1.47/0.98  fd_cond                                 0
% 1.47/0.98  fd_pseudo_cond                          1
% 1.47/0.98  AC symbols                              0
% 1.47/0.98  
% 1.47/0.98  ------ Schedule dynamic 5 is on 
% 1.47/0.98  
% 1.47/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  ------ 
% 1.47/0.98  Current options:
% 1.47/0.98  ------ 
% 1.47/0.98  
% 1.47/0.98  ------ Input Options
% 1.47/0.98  
% 1.47/0.98  --out_options                           all
% 1.47/0.98  --tptp_safe_out                         true
% 1.47/0.98  --problem_path                          ""
% 1.47/0.98  --include_path                          ""
% 1.47/0.98  --clausifier                            res/vclausify_rel
% 1.47/0.98  --clausifier_options                    --mode clausify
% 1.47/0.98  --stdin                                 false
% 1.47/0.98  --stats_out                             all
% 1.47/0.98  
% 1.47/0.98  ------ General Options
% 1.47/0.98  
% 1.47/0.98  --fof                                   false
% 1.47/0.98  --time_out_real                         305.
% 1.47/0.98  --time_out_virtual                      -1.
% 1.47/0.98  --symbol_type_check                     false
% 1.47/0.98  --clausify_out                          false
% 1.47/0.98  --sig_cnt_out                           false
% 1.47/0.98  --trig_cnt_out                          false
% 1.47/0.98  --trig_cnt_out_tolerance                1.
% 1.47/0.98  --trig_cnt_out_sk_spl                   false
% 1.47/0.98  --abstr_cl_out                          false
% 1.47/0.98  
% 1.47/0.98  ------ Global Options
% 1.47/0.98  
% 1.47/0.98  --schedule                              default
% 1.47/0.98  --add_important_lit                     false
% 1.47/0.98  --prop_solver_per_cl                    1000
% 1.47/0.98  --min_unsat_core                        false
% 1.47/0.98  --soft_assumptions                      false
% 1.47/0.98  --soft_lemma_size                       3
% 1.47/0.98  --prop_impl_unit_size                   0
% 1.47/0.98  --prop_impl_unit                        []
% 1.47/0.98  --share_sel_clauses                     true
% 1.47/0.98  --reset_solvers                         false
% 1.47/0.98  --bc_imp_inh                            [conj_cone]
% 1.47/0.98  --conj_cone_tolerance                   3.
% 1.47/0.98  --extra_neg_conj                        none
% 1.47/0.98  --large_theory_mode                     true
% 1.47/0.98  --prolific_symb_bound                   200
% 1.47/0.98  --lt_threshold                          2000
% 1.47/0.98  --clause_weak_htbl                      true
% 1.47/0.98  --gc_record_bc_elim                     false
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing Options
% 1.47/0.98  
% 1.47/0.98  --preprocessing_flag                    true
% 1.47/0.98  --time_out_prep_mult                    0.1
% 1.47/0.98  --splitting_mode                        input
% 1.47/0.98  --splitting_grd                         true
% 1.47/0.98  --splitting_cvd                         false
% 1.47/0.98  --splitting_cvd_svl                     false
% 1.47/0.98  --splitting_nvd                         32
% 1.47/0.98  --sub_typing                            true
% 1.47/0.98  --prep_gs_sim                           true
% 1.47/0.98  --prep_unflatten                        true
% 1.47/0.98  --prep_res_sim                          true
% 1.47/0.98  --prep_upred                            true
% 1.47/0.98  --prep_sem_filter                       exhaustive
% 1.47/0.98  --prep_sem_filter_out                   false
% 1.47/0.98  --pred_elim                             true
% 1.47/0.98  --res_sim_input                         true
% 1.47/0.98  --eq_ax_congr_red                       true
% 1.47/0.98  --pure_diseq_elim                       true
% 1.47/0.98  --brand_transform                       false
% 1.47/0.98  --non_eq_to_eq                          false
% 1.47/0.98  --prep_def_merge                        true
% 1.47/0.98  --prep_def_merge_prop_impl              false
% 1.47/0.98  --prep_def_merge_mbd                    true
% 1.47/0.98  --prep_def_merge_tr_red                 false
% 1.47/0.98  --prep_def_merge_tr_cl                  false
% 1.47/0.98  --smt_preprocessing                     true
% 1.47/0.98  --smt_ac_axioms                         fast
% 1.47/0.98  --preprocessed_out                      false
% 1.47/0.98  --preprocessed_stats                    false
% 1.47/0.98  
% 1.47/0.98  ------ Abstraction refinement Options
% 1.47/0.98  
% 1.47/0.98  --abstr_ref                             []
% 1.47/0.98  --abstr_ref_prep                        false
% 1.47/0.98  --abstr_ref_until_sat                   false
% 1.47/0.98  --abstr_ref_sig_restrict                funpre
% 1.47/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.47/0.98  --abstr_ref_under                       []
% 1.47/0.98  
% 1.47/0.98  ------ SAT Options
% 1.47/0.98  
% 1.47/0.98  --sat_mode                              false
% 1.47/0.98  --sat_fm_restart_options                ""
% 1.47/0.98  --sat_gr_def                            false
% 1.47/0.98  --sat_epr_types                         true
% 1.47/0.98  --sat_non_cyclic_types                  false
% 1.47/0.98  --sat_finite_models                     false
% 1.47/0.98  --sat_fm_lemmas                         false
% 1.47/0.98  --sat_fm_prep                           false
% 1.47/0.98  --sat_fm_uc_incr                        true
% 1.47/0.98  --sat_out_model                         small
% 1.47/0.98  --sat_out_clauses                       false
% 1.47/0.98  
% 1.47/0.98  ------ QBF Options
% 1.47/0.98  
% 1.47/0.98  --qbf_mode                              false
% 1.47/0.98  --qbf_elim_univ                         false
% 1.47/0.98  --qbf_dom_inst                          none
% 1.47/0.98  --qbf_dom_pre_inst                      false
% 1.47/0.98  --qbf_sk_in                             false
% 1.47/0.98  --qbf_pred_elim                         true
% 1.47/0.98  --qbf_split                             512
% 1.47/0.98  
% 1.47/0.98  ------ BMC1 Options
% 1.47/0.98  
% 1.47/0.98  --bmc1_incremental                      false
% 1.47/0.98  --bmc1_axioms                           reachable_all
% 1.47/0.98  --bmc1_min_bound                        0
% 1.47/0.98  --bmc1_max_bound                        -1
% 1.47/0.98  --bmc1_max_bound_default                -1
% 1.47/0.98  --bmc1_symbol_reachability              true
% 1.47/0.98  --bmc1_property_lemmas                  false
% 1.47/0.98  --bmc1_k_induction                      false
% 1.47/0.98  --bmc1_non_equiv_states                 false
% 1.47/0.98  --bmc1_deadlock                         false
% 1.47/0.98  --bmc1_ucm                              false
% 1.47/0.98  --bmc1_add_unsat_core                   none
% 1.47/0.98  --bmc1_unsat_core_children              false
% 1.47/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.47/0.98  --bmc1_out_stat                         full
% 1.47/0.98  --bmc1_ground_init                      false
% 1.47/0.98  --bmc1_pre_inst_next_state              false
% 1.47/0.98  --bmc1_pre_inst_state                   false
% 1.47/0.98  --bmc1_pre_inst_reach_state             false
% 1.47/0.98  --bmc1_out_unsat_core                   false
% 1.47/0.98  --bmc1_aig_witness_out                  false
% 1.47/0.98  --bmc1_verbose                          false
% 1.47/0.98  --bmc1_dump_clauses_tptp                false
% 1.47/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.47/0.98  --bmc1_dump_file                        -
% 1.47/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.47/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.47/0.98  --bmc1_ucm_extend_mode                  1
% 1.47/0.98  --bmc1_ucm_init_mode                    2
% 1.47/0.98  --bmc1_ucm_cone_mode                    none
% 1.47/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.47/0.98  --bmc1_ucm_relax_model                  4
% 1.47/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.47/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.47/0.98  --bmc1_ucm_layered_model                none
% 1.47/0.98  --bmc1_ucm_max_lemma_size               10
% 1.47/0.98  
% 1.47/0.98  ------ AIG Options
% 1.47/0.98  
% 1.47/0.98  --aig_mode                              false
% 1.47/0.98  
% 1.47/0.98  ------ Instantiation Options
% 1.47/0.98  
% 1.47/0.98  --instantiation_flag                    true
% 1.47/0.98  --inst_sos_flag                         false
% 1.47/0.98  --inst_sos_phase                        true
% 1.47/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.47/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.47/0.98  --inst_lit_sel_side                     none
% 1.47/0.98  --inst_solver_per_active                1400
% 1.47/0.98  --inst_solver_calls_frac                1.
% 1.47/0.98  --inst_passive_queue_type               priority_queues
% 1.47/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.47/0.98  --inst_passive_queues_freq              [25;2]
% 1.47/0.98  --inst_dismatching                      true
% 1.47/0.98  --inst_eager_unprocessed_to_passive     true
% 1.47/0.98  --inst_prop_sim_given                   true
% 1.47/0.98  --inst_prop_sim_new                     false
% 1.47/0.98  --inst_subs_new                         false
% 1.47/0.98  --inst_eq_res_simp                      false
% 1.47/0.98  --inst_subs_given                       false
% 1.47/0.98  --inst_orphan_elimination               true
% 1.47/0.98  --inst_learning_loop_flag               true
% 1.47/0.98  --inst_learning_start                   3000
% 1.47/0.98  --inst_learning_factor                  2
% 1.47/0.98  --inst_start_prop_sim_after_learn       3
% 1.47/0.98  --inst_sel_renew                        solver
% 1.47/0.98  --inst_lit_activity_flag                true
% 1.47/0.98  --inst_restr_to_given                   false
% 1.47/0.98  --inst_activity_threshold               500
% 1.47/0.98  --inst_out_proof                        true
% 1.47/0.98  
% 1.47/0.98  ------ Resolution Options
% 1.47/0.98  
% 1.47/0.98  --resolution_flag                       false
% 1.47/0.98  --res_lit_sel                           adaptive
% 1.47/0.98  --res_lit_sel_side                      none
% 1.47/0.98  --res_ordering                          kbo
% 1.47/0.98  --res_to_prop_solver                    active
% 1.47/0.98  --res_prop_simpl_new                    false
% 1.47/0.98  --res_prop_simpl_given                  true
% 1.47/0.98  --res_passive_queue_type                priority_queues
% 1.47/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.47/0.98  --res_passive_queues_freq               [15;5]
% 1.47/0.98  --res_forward_subs                      full
% 1.47/0.98  --res_backward_subs                     full
% 1.47/0.98  --res_forward_subs_resolution           true
% 1.47/0.98  --res_backward_subs_resolution          true
% 1.47/0.98  --res_orphan_elimination                true
% 1.47/0.98  --res_time_limit                        2.
% 1.47/0.98  --res_out_proof                         true
% 1.47/0.98  
% 1.47/0.98  ------ Superposition Options
% 1.47/0.98  
% 1.47/0.98  --superposition_flag                    true
% 1.47/0.98  --sup_passive_queue_type                priority_queues
% 1.47/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.47/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.47/0.98  --demod_completeness_check              fast
% 1.47/0.98  --demod_use_ground                      true
% 1.47/0.98  --sup_to_prop_solver                    passive
% 1.47/0.98  --sup_prop_simpl_new                    true
% 1.47/0.98  --sup_prop_simpl_given                  true
% 1.47/0.98  --sup_fun_splitting                     false
% 1.47/0.98  --sup_smt_interval                      50000
% 1.47/0.98  
% 1.47/0.98  ------ Superposition Simplification Setup
% 1.47/0.98  
% 1.47/0.98  --sup_indices_passive                   []
% 1.47/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.47/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_full_bw                           [BwDemod]
% 1.47/0.98  --sup_immed_triv                        [TrivRules]
% 1.47/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.47/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_immed_bw_main                     []
% 1.47/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.47/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/0.98  
% 1.47/0.98  ------ Combination Options
% 1.47/0.98  
% 1.47/0.98  --comb_res_mult                         3
% 1.47/0.98  --comb_sup_mult                         2
% 1.47/0.98  --comb_inst_mult                        10
% 1.47/0.98  
% 1.47/0.98  ------ Debug Options
% 1.47/0.98  
% 1.47/0.98  --dbg_backtrace                         false
% 1.47/0.98  --dbg_dump_prop_clauses                 false
% 1.47/0.98  --dbg_dump_prop_clauses_file            -
% 1.47/0.98  --dbg_out_stat                          false
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  ------ Proving...
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  % SZS status Theorem for theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  fof(f1,axiom,(
% 1.47/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f12,plain,(
% 1.47/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.98    inference(ennf_transformation,[],[f1])).
% 1.47/0.98  
% 1.47/0.98  fof(f25,plain,(
% 1.47/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.98    inference(nnf_transformation,[],[f12])).
% 1.47/0.98  
% 1.47/0.98  fof(f26,plain,(
% 1.47/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.98    inference(rectify,[],[f25])).
% 1.47/0.98  
% 1.47/0.98  fof(f27,plain,(
% 1.47/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.47/0.98    introduced(choice_axiom,[])).
% 1.47/0.98  
% 1.47/0.98  fof(f28,plain,(
% 1.47/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.47/0.98  
% 1.47/0.98  fof(f35,plain,(
% 1.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f28])).
% 1.47/0.98  
% 1.47/0.98  fof(f4,axiom,(
% 1.47/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f41,plain,(
% 1.47/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.47/0.98    inference(cnf_transformation,[],[f4])).
% 1.47/0.98  
% 1.47/0.98  fof(f6,axiom,(
% 1.47/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f16,plain,(
% 1.47/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.98    inference(ennf_transformation,[],[f6])).
% 1.47/0.98  
% 1.47/0.98  fof(f43,plain,(
% 1.47/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f16])).
% 1.47/0.98  
% 1.47/0.98  fof(f8,axiom,(
% 1.47/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f19,plain,(
% 1.47/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.98    inference(ennf_transformation,[],[f8])).
% 1.47/0.98  
% 1.47/0.98  fof(f20,plain,(
% 1.47/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.98    inference(flattening,[],[f19])).
% 1.47/0.98  
% 1.47/0.98  fof(f46,plain,(
% 1.47/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f20])).
% 1.47/0.98  
% 1.47/0.98  fof(f10,conjecture,(
% 1.47/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f11,negated_conjecture,(
% 1.47/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.47/0.98    inference(negated_conjecture,[],[f10])).
% 1.47/0.98  
% 1.47/0.98  fof(f23,plain,(
% 1.47/0.98    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.98    inference(ennf_transformation,[],[f11])).
% 1.47/0.98  
% 1.47/0.98  fof(f24,plain,(
% 1.47/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.98    inference(flattening,[],[f23])).
% 1.47/0.98  
% 1.47/0.98  fof(f32,plain,(
% 1.47/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK4) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK4,X0,X1) & v1_funct_1(sK4))) )),
% 1.47/0.98    introduced(choice_axiom,[])).
% 1.47/0.98  
% 1.47/0.98  fof(f31,plain,(
% 1.47/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.47/0.98    introduced(choice_axiom,[])).
% 1.47/0.98  
% 1.47/0.98  fof(f33,plain,(
% 1.47/0.98    (~r2_relset_1(sK1,sK2,sK3,sK4) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f32,f31])).
% 1.47/0.98  
% 1.47/0.98  fof(f49,plain,(
% 1.47/0.98    v1_funct_2(sK3,sK1,sK2)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f48,plain,(
% 1.47/0.98    v1_funct_1(sK3)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f50,plain,(
% 1.47/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f52,plain,(
% 1.47/0.98    v1_funct_2(sK4,sK1,sK2)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f51,plain,(
% 1.47/0.98    v1_funct_1(sK4)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f53,plain,(
% 1.47/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f9,axiom,(
% 1.47/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f21,plain,(
% 1.47/0.98    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.98    inference(ennf_transformation,[],[f9])).
% 1.47/0.98  
% 1.47/0.98  fof(f22,plain,(
% 1.47/0.98    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.98    inference(flattening,[],[f21])).
% 1.47/0.98  
% 1.47/0.98  fof(f47,plain,(
% 1.47/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f22])).
% 1.47/0.98  
% 1.47/0.98  fof(f54,plain,(
% 1.47/0.98    r1_partfun1(sK3,sK4)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f7,axiom,(
% 1.47/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f17,plain,(
% 1.47/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.47/0.98    inference(ennf_transformation,[],[f7])).
% 1.47/0.98  
% 1.47/0.98  fof(f18,plain,(
% 1.47/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.98    inference(flattening,[],[f17])).
% 1.47/0.98  
% 1.47/0.98  fof(f44,plain,(
% 1.47/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.98    inference(cnf_transformation,[],[f18])).
% 1.47/0.98  
% 1.47/0.98  fof(f56,plain,(
% 1.47/0.98    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 1.47/0.98    inference(cnf_transformation,[],[f33])).
% 1.47/0.98  
% 1.47/0.98  fof(f3,axiom,(
% 1.47/0.98    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f13,plain,(
% 1.47/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.47/0.98    inference(ennf_transformation,[],[f3])).
% 1.47/0.98  
% 1.47/0.98  fof(f40,plain,(
% 1.47/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f13])).
% 1.47/0.98  
% 1.47/0.98  fof(f2,axiom,(
% 1.47/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.47/0.98  
% 1.47/0.98  fof(f29,plain,(
% 1.47/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.98    inference(nnf_transformation,[],[f2])).
% 1.47/0.98  
% 1.47/0.98  fof(f30,plain,(
% 1.47/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.98    inference(flattening,[],[f29])).
% 1.47/0.98  
% 1.47/0.98  fof(f39,plain,(
% 1.47/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.47/0.98    inference(cnf_transformation,[],[f30])).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1,plain,
% 1.47/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.47/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_720,plain,
% 1.47/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.47/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_7,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.47/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_715,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_9,plain,
% 1.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.47/0.98      | ~ r2_hidden(X2,X0)
% 1.47/0.98      | ~ v1_xboole_0(X1) ),
% 1.47/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_713,plain,
% 1.47/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.47/0.98      | r2_hidden(X2,X0) != iProver_top
% 1.47/0.98      | v1_xboole_0(X1) != iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1127,plain,
% 1.47/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 1.47/0.98      | v1_xboole_0(X1) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_715,c_713]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_11,plain,
% 1.47/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.47/0.98      | v1_partfun1(X0,X1)
% 1.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.47/0.98      | ~ v1_funct_1(X0)
% 1.47/0.98      | v1_xboole_0(X2) ),
% 1.47/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_21,negated_conjecture,
% 1.47/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.47/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_291,plain,
% 1.47/0.98      ( v1_partfun1(X0,X1)
% 1.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.47/0.98      | ~ v1_funct_1(X0)
% 1.47/0.98      | v1_xboole_0(X2)
% 1.47/0.98      | sK3 != X0
% 1.47/0.98      | sK2 != X2
% 1.47/0.98      | sK1 != X1 ),
% 1.47/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_292,plain,
% 1.47/0.98      ( v1_partfun1(sK3,sK1)
% 1.47/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | ~ v1_funct_1(sK3)
% 1.47/0.98      | v1_xboole_0(sK2) ),
% 1.47/0.98      inference(unflattening,[status(thm)],[c_291]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_22,negated_conjecture,
% 1.47/0.98      ( v1_funct_1(sK3) ),
% 1.47/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_20,negated_conjecture,
% 1.47/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.47/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_294,plain,
% 1.47/0.98      ( v1_partfun1(sK3,sK1) | v1_xboole_0(sK2) ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_292,c_22,c_20]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_707,plain,
% 1.47/0.98      ( v1_partfun1(sK3,sK1) = iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_18,negated_conjecture,
% 1.47/0.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 1.47/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_277,plain,
% 1.47/0.98      ( v1_partfun1(X0,X1)
% 1.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.47/0.98      | ~ v1_funct_1(X0)
% 1.47/0.98      | v1_xboole_0(X2)
% 1.47/0.98      | sK4 != X0
% 1.47/0.98      | sK2 != X2
% 1.47/0.98      | sK1 != X1 ),
% 1.47/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_278,plain,
% 1.47/0.98      ( v1_partfun1(sK4,sK1)
% 1.47/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | ~ v1_funct_1(sK4)
% 1.47/0.98      | v1_xboole_0(sK2) ),
% 1.47/0.98      inference(unflattening,[status(thm)],[c_277]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_19,negated_conjecture,
% 1.47/0.98      ( v1_funct_1(sK4) ),
% 1.47/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_17,negated_conjecture,
% 1.47/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.47/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_280,plain,
% 1.47/0.98      ( v1_partfun1(sK4,sK1) | v1_xboole_0(sK2) ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_278,c_19,c_17]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_282,plain,
% 1.47/0.98      ( v1_partfun1(sK4,sK1) = iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_296,plain,
% 1.47/0.98      ( v1_partfun1(sK3,sK1) = iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_417,plain,( X0 = X0 ),theory(equality) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_905,plain,
% 1.47/0.98      ( sK3 = sK3 ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_417]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_712,plain,
% 1.47/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_13,plain,
% 1.47/0.98      ( ~ r1_partfun1(X0,X1)
% 1.47/0.98      | ~ v1_partfun1(X1,X2)
% 1.47/0.98      | ~ v1_partfun1(X0,X2)
% 1.47/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.47/0.98      | ~ v1_funct_1(X0)
% 1.47/0.98      | ~ v1_funct_1(X1)
% 1.47/0.98      | X0 = X1 ),
% 1.47/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_16,negated_conjecture,
% 1.47/0.98      ( r1_partfun1(sK3,sK4) ),
% 1.47/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_244,plain,
% 1.47/0.98      ( ~ v1_partfun1(X0,X1)
% 1.47/0.98      | ~ v1_partfun1(X2,X1)
% 1.47/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.47/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.47/0.98      | ~ v1_funct_1(X2)
% 1.47/0.98      | ~ v1_funct_1(X0)
% 1.47/0.98      | X0 = X2
% 1.47/0.98      | sK4 != X0
% 1.47/0.98      | sK3 != X2 ),
% 1.47/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_245,plain,
% 1.47/0.98      ( ~ v1_partfun1(sK4,X0)
% 1.47/0.98      | ~ v1_partfun1(sK3,X0)
% 1.47/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.47/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.47/0.98      | ~ v1_funct_1(sK4)
% 1.47/0.98      | ~ v1_funct_1(sK3)
% 1.47/0.98      | sK4 = sK3 ),
% 1.47/0.98      inference(unflattening,[status(thm)],[c_244]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_249,plain,
% 1.47/0.98      ( ~ v1_partfun1(sK4,X0)
% 1.47/0.98      | ~ v1_partfun1(sK3,X0)
% 1.47/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.47/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.47/0.98      | sK4 = sK3 ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_245,c_22,c_19]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_709,plain,
% 1.47/0.98      ( sK4 = sK3
% 1.47/0.98      | v1_partfun1(sK4,X0) != iProver_top
% 1.47/0.98      | v1_partfun1(sK3,X0) != iProver_top
% 1.47/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.47/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_923,plain,
% 1.47/0.98      ( sK4 = sK3
% 1.47/0.98      | v1_partfun1(sK4,sK1) != iProver_top
% 1.47/0.98      | v1_partfun1(sK3,sK1) != iProver_top
% 1.47/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_712,c_709]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_25,plain,
% 1.47/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_926,plain,
% 1.47/0.98      ( v1_partfun1(sK3,sK1) != iProver_top
% 1.47/0.98      | v1_partfun1(sK4,sK1) != iProver_top
% 1.47/0.98      | sK4 = sK3 ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_923,c_25]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_927,plain,
% 1.47/0.98      ( sK4 = sK3
% 1.47/0.98      | v1_partfun1(sK4,sK1) != iProver_top
% 1.47/0.98      | v1_partfun1(sK3,sK1) != iProver_top ),
% 1.47/0.98      inference(renaming,[status(thm)],[c_926]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_418,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_841,plain,
% 1.47/0.98      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_418]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_946,plain,
% 1.47/0.98      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_841]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_10,plain,
% 1.47/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 1.47/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.47/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.47/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_14,negated_conjecture,
% 1.47/0.98      ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
% 1.47/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_223,plain,
% 1.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.47/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.47/0.98      | sK4 != X0
% 1.47/0.98      | sK3 != X0
% 1.47/0.98      | sK2 != X2
% 1.47/0.98      | sK1 != X1 ),
% 1.47/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_224,plain,
% 1.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | sK3 != sK4 ),
% 1.47/0.98      inference(unflattening,[status(thm)],[c_223]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_228,plain,
% 1.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | sK3 != sK4 ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_224,c_17]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_972,plain,
% 1.47/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.47/0.98      | sK3 != sK4 ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_228]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_973,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1000,plain,
% 1.47/0.98      ( v1_xboole_0(sK2) = iProver_top ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_707,c_282,c_296,c_905,c_927,c_946,c_972,c_973]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1176,plain,
% 1.47/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 1.47/0.98      | ~ r2_hidden(X1,X0)
% 1.47/0.98      | ~ v1_xboole_0(sK2) ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1348,plain,
% 1.47/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 1.47/0.98      | ~ r2_hidden(X0,k1_xboole_0)
% 1.47/0.98      | ~ v1_xboole_0(sK2) ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_1176]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1350,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
% 1.47/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1348]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1349,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1354,plain,
% 1.47/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1349]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1357,plain,
% 1.47/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_1127,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1350,
% 1.47/0.98                 c_1354]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1364,plain,
% 1.47/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_720,c_1357]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_711,plain,
% 1.47/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1015,plain,
% 1.47/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 1.47/0.98      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_711,c_713]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_6,plain,
% 1.47/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 1.47/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1182,plain,
% 1.47/0.98      ( v1_xboole_0(k2_zfmisc_1(X0,sK2)) | ~ v1_xboole_0(sK2) ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1183,plain,
% 1.47/0.98      ( v1_xboole_0(k2_zfmisc_1(X0,sK2)) = iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1185,plain,
% 1.47/0.98      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) = iProver_top
% 1.47/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_1183]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1225,plain,
% 1.47/0.98      ( r2_hidden(X0,sK3) != iProver_top ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_1015,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1185]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1232,plain,
% 1.47/0.98      ( r1_tarski(sK3,X0) = iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_720,c_1225]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_3,plain,
% 1.47/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.47/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_718,plain,
% 1.47/0.98      ( X0 = X1
% 1.47/0.98      | r1_tarski(X1,X0) != iProver_top
% 1.47/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 1.47/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1421,plain,
% 1.47/0.98      ( sK3 = X0 | r1_tarski(X0,sK3) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_1232,c_718]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1615,plain,
% 1.47/0.98      ( sK3 = k1_xboole_0 ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_1364,c_1421]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1014,plain,
% 1.47/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 1.47/0.98      | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_712,c_713]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1213,plain,
% 1.47/0.98      ( r2_hidden(X0,sK4) != iProver_top ),
% 1.47/0.98      inference(global_propositional_subsumption,
% 1.47/0.98                [status(thm)],
% 1.47/0.98                [c_1014,c_282,c_296,c_905,c_927,c_946,c_972,c_973,c_1185]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1220,plain,
% 1.47/0.98      ( r1_tarski(sK4,X0) = iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_720,c_1213]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1420,plain,
% 1.47/0.98      ( sK4 = X0 | r1_tarski(X0,sK4) != iProver_top ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_1220,c_718]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1603,plain,
% 1.47/0.98      ( sK4 = k1_xboole_0 ),
% 1.47/0.98      inference(superposition,[status(thm)],[c_1364,c_1420]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(c_1535,plain,
% 1.47/0.98      ( sK4 != k1_xboole_0 | sK3 = sK4 | sK3 != k1_xboole_0 ),
% 1.47/0.98      inference(instantiation,[status(thm)],[c_841]) ).
% 1.47/0.98  
% 1.47/0.98  cnf(contradiction,plain,
% 1.47/0.98      ( $false ),
% 1.47/0.98      inference(minisat,[status(thm)],[c_1615,c_1603,c_1535,c_973,c_972]) ).
% 1.47/0.98  
% 1.47/0.98  
% 1.47/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.47/0.98  
% 1.47/0.98  ------                               Statistics
% 1.47/0.98  
% 1.47/0.98  ------ General
% 1.47/0.98  
% 1.47/0.98  abstr_ref_over_cycles:                  0
% 1.47/0.98  abstr_ref_under_cycles:                 0
% 1.47/0.98  gc_basic_clause_elim:                   0
% 1.47/0.98  forced_gc_time:                         0
% 1.47/0.98  parsing_time:                           0.009
% 1.47/0.98  unif_index_cands_time:                  0.
% 1.47/0.98  unif_index_add_time:                    0.
% 1.47/0.98  orderings_time:                         0.
% 1.47/0.98  out_proof_time:                         0.012
% 1.47/0.98  total_time:                             0.078
% 1.47/0.98  num_of_symbols:                         48
% 1.47/0.98  num_of_terms:                           1241
% 1.47/0.98  
% 1.47/0.98  ------ Preprocessing
% 1.47/0.98  
% 1.47/0.98  num_of_splits:                          0
% 1.47/0.98  num_of_split_atoms:                     0
% 1.47/0.98  num_of_reused_defs:                     0
% 1.47/0.98  num_eq_ax_congr_red:                    17
% 1.47/0.98  num_of_sem_filtered_clauses:            1
% 1.47/0.98  num_of_subtypes:                        0
% 1.47/0.98  monotx_restored_types:                  0
% 1.47/0.98  sat_num_of_epr_types:                   0
% 1.47/0.98  sat_num_of_non_cyclic_types:            0
% 1.47/0.98  sat_guarded_non_collapsed_types:        0
% 1.47/0.98  num_pure_diseq_elim:                    0
% 1.47/0.98  simp_replaced_by:                       0
% 1.47/0.98  res_preprocessed:                       86
% 1.47/0.98  prep_upred:                             0
% 1.47/0.98  prep_unflattend:                        11
% 1.47/0.98  smt_new_axioms:                         0
% 1.47/0.98  pred_elim_cands:                        5
% 1.47/0.98  pred_elim:                              4
% 1.47/0.98  pred_elim_cl:                           5
% 1.47/0.98  pred_elim_cycles:                       6
% 1.47/0.98  merged_defs:                            0
% 1.47/0.98  merged_defs_ncl:                        0
% 1.47/0.98  bin_hyper_res:                          0
% 1.47/0.98  prep_cycles:                            4
% 1.47/0.98  pred_elim_time:                         0.002
% 1.47/0.98  splitting_time:                         0.
% 1.47/0.98  sem_filter_time:                        0.
% 1.47/0.98  monotx_time:                            0.
% 1.47/0.98  subtype_inf_time:                       0.
% 1.47/0.98  
% 1.47/0.98  ------ Problem properties
% 1.47/0.98  
% 1.47/0.98  clauses:                                16
% 1.47/0.98  conjectures:                            3
% 1.47/0.98  epr:                                    6
% 1.47/0.98  horn:                                   13
% 1.47/0.98  ground:                                 5
% 1.47/0.98  unary:                                  4
% 1.47/0.98  binary:                                 7
% 1.47/0.98  lits:                                   35
% 1.47/0.98  lits_eq:                                5
% 1.47/0.99  fd_pure:                                0
% 1.47/0.99  fd_pseudo:                              0
% 1.47/0.99  fd_cond:                                0
% 1.47/0.99  fd_pseudo_cond:                         1
% 1.47/0.99  ac_symbols:                             0
% 1.47/0.99  
% 1.47/0.99  ------ Propositional Solver
% 1.47/0.99  
% 1.47/0.99  prop_solver_calls:                      26
% 1.47/0.99  prop_fast_solver_calls:                 486
% 1.47/0.99  smt_solver_calls:                       0
% 1.47/0.99  smt_fast_solver_calls:                  0
% 1.47/0.99  prop_num_of_clauses:                    512
% 1.47/0.99  prop_preprocess_simplified:             2723
% 1.47/0.99  prop_fo_subsumed:                       13
% 1.47/0.99  prop_solver_time:                       0.
% 1.47/0.99  smt_solver_time:                        0.
% 1.47/0.99  smt_fast_solver_time:                   0.
% 1.47/0.99  prop_fast_solver_time:                  0.
% 1.47/0.99  prop_unsat_core_time:                   0.
% 1.47/0.99  
% 1.47/0.99  ------ QBF
% 1.47/0.99  
% 1.47/0.99  qbf_q_res:                              0
% 1.47/0.99  qbf_num_tautologies:                    0
% 1.47/0.99  qbf_prep_cycles:                        0
% 1.47/0.99  
% 1.47/0.99  ------ BMC1
% 1.47/0.99  
% 1.47/0.99  bmc1_current_bound:                     -1
% 1.47/0.99  bmc1_last_solved_bound:                 -1
% 1.47/0.99  bmc1_unsat_core_size:                   -1
% 1.47/0.99  bmc1_unsat_core_parents_size:           -1
% 1.47/0.99  bmc1_merge_next_fun:                    0
% 1.47/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.47/0.99  
% 1.47/0.99  ------ Instantiation
% 1.47/0.99  
% 1.47/0.99  inst_num_of_clauses:                    155
% 1.47/0.99  inst_num_in_passive:                    16
% 1.47/0.99  inst_num_in_active:                     92
% 1.47/0.99  inst_num_in_unprocessed:                47
% 1.47/0.99  inst_num_of_loops:                      120
% 1.47/0.99  inst_num_of_learning_restarts:          0
% 1.47/0.99  inst_num_moves_active_passive:          26
% 1.47/0.99  inst_lit_activity:                      0
% 1.47/0.99  inst_lit_activity_moves:                0
% 1.47/0.99  inst_num_tautologies:                   0
% 1.47/0.99  inst_num_prop_implied:                  0
% 1.47/0.99  inst_num_existing_simplified:           0
% 1.47/0.99  inst_num_eq_res_simplified:             0
% 1.47/0.99  inst_num_child_elim:                    0
% 1.47/0.99  inst_num_of_dismatching_blockings:      12
% 1.47/0.99  inst_num_of_non_proper_insts:           129
% 1.47/0.99  inst_num_of_duplicates:                 0
% 1.47/0.99  inst_inst_num_from_inst_to_res:         0
% 1.47/0.99  inst_dismatching_checking_time:         0.
% 1.47/0.99  
% 1.47/0.99  ------ Resolution
% 1.47/0.99  
% 1.47/0.99  res_num_of_clauses:                     0
% 1.47/0.99  res_num_in_passive:                     0
% 1.47/0.99  res_num_in_active:                      0
% 1.47/0.99  res_num_of_loops:                       90
% 1.47/0.99  res_forward_subset_subsumed:            16
% 1.47/0.99  res_backward_subset_subsumed:           0
% 1.47/0.99  res_forward_subsumed:                   0
% 1.47/0.99  res_backward_subsumed:                  0
% 1.47/0.99  res_forward_subsumption_resolution:     0
% 1.47/0.99  res_backward_subsumption_resolution:    0
% 1.47/0.99  res_clause_to_clause_subsumption:       54
% 1.47/0.99  res_orphan_elimination:                 0
% 1.47/0.99  res_tautology_del:                      12
% 1.47/0.99  res_num_eq_res_simplified:              0
% 1.47/0.99  res_num_sel_changes:                    0
% 1.47/0.99  res_moves_from_active_to_pass:          0
% 1.47/0.99  
% 1.47/0.99  ------ Superposition
% 1.47/0.99  
% 1.47/0.99  sup_time_total:                         0.
% 1.47/0.99  sup_time_generating:                    0.
% 1.47/0.99  sup_time_sim_full:                      0.
% 1.47/0.99  sup_time_sim_immed:                     0.
% 1.47/0.99  
% 1.47/0.99  sup_num_of_clauses:                     27
% 1.47/0.99  sup_num_in_active:                      23
% 1.47/0.99  sup_num_in_passive:                     4
% 1.47/0.99  sup_num_of_loops:                       23
% 1.47/0.99  sup_fw_superposition:                   23
% 1.47/0.99  sup_bw_superposition:                   1
% 1.47/0.99  sup_immediate_simplified:               3
% 1.47/0.99  sup_given_eliminated:                   2
% 1.47/0.99  comparisons_done:                       0
% 1.47/0.99  comparisons_avoided:                    0
% 1.47/0.99  
% 1.47/0.99  ------ Simplifications
% 1.47/0.99  
% 1.47/0.99  
% 1.47/0.99  sim_fw_subset_subsumed:                 3
% 1.47/0.99  sim_bw_subset_subsumed:                 0
% 1.47/0.99  sim_fw_subsumed:                        0
% 1.47/0.99  sim_bw_subsumed:                        0
% 1.47/0.99  sim_fw_subsumption_res:                 0
% 1.47/0.99  sim_bw_subsumption_res:                 0
% 1.47/0.99  sim_tautology_del:                      0
% 1.47/0.99  sim_eq_tautology_del:                   1
% 1.47/0.99  sim_eq_res_simp:                        0
% 1.47/0.99  sim_fw_demodulated:                     0
% 1.47/0.99  sim_bw_demodulated:                     2
% 1.47/0.99  sim_light_normalised:                   0
% 1.47/0.99  sim_joinable_taut:                      0
% 1.47/0.99  sim_joinable_simp:                      0
% 1.47/0.99  sim_ac_normalised:                      0
% 1.47/0.99  sim_smt_subsumption:                    0
% 1.47/0.99  
%------------------------------------------------------------------------------
