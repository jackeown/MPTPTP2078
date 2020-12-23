%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0822+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:10 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  112 (2011 expanded)
%              Number of clauses        :   68 ( 623 expanded)
%              Number of leaves         :   15 ( 538 expanded)
%              Depth                    :   23
%              Number of atoms          :  334 (8219 expanded)
%              Number of equality atoms :  166 (2506 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X2,X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
     => r2_hidden(k4_tarski(sK7(X5),X5),X2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
          & r2_hidden(X3,X1) )
     => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK6),X2)
        & r2_hidden(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK3,sK4,sK5) != sK4
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK5)
            & r2_hidden(X3,sK4) ) )
      & ( k2_relset_1(sK3,sK4,sK5) = sK4
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK5)
            | ~ r2_hidden(X5,sK4) ) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k2_relset_1(sK3,sK4,sK5) != sK4
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK6),sK5)
        & r2_hidden(sK6,sK4) ) )
    & ( k2_relset_1(sK3,sK4,sK5) = sK4
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK7(X5),X5),sK5)
          | ~ r2_hidden(X5,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X5] :
      ( k2_relset_1(sK3,sK4,sK5) = sK4
      | r2_hidden(k4_tarski(sK7(X5),X5),sK5)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X4] :
      ( k2_relset_1(sK3,sK4,sK5) != sK4
      | ~ r2_hidden(k4_tarski(X4,sK6),sK5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    | r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_419,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_421,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_420,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1406,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_420])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_410,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_417,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_705,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_410,c_417])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_418,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1027,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_418])).

cnf(c_13,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1375,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1027,c_13])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_415,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1381,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_415])).

cnf(c_4459,plain,
    ( k2_relat_1(sK5) = X0
    | m1_subset_1(sK0(sK5,X0),sK4) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_1381])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k4_tarski(sK7(X0),X0),sK5)
    | k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_411,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7(X0),X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_594,plain,
    ( k2_relset_1(sK3,sK4,sK5) = sK4
    | r2_hidden(X0,k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_411,c_420])).

cnf(c_984,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(X0,k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_705,c_594])).

cnf(c_1628,plain,
    ( k2_relat_1(sK5) = sK4
    | m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_1381])).

cnf(c_4800,plain,
    ( k2_relat_1(sK5) = sK4
    | m1_subset_1(sK0(sK5,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_1628])).

cnf(c_985,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK7(X0),X0),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_705,c_411])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK0(X1,X2)),X1)
    | ~ r2_hidden(sK0(X1,X2),X2)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_422,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(X2,sK0(X0,X1)),X0) != iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1466,plain,
    ( k2_relat_1(sK5) = X0
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | r2_hidden(sK0(sK5,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_422])).

cnf(c_1485,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1382,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_414])).

cnf(c_1627,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_1382])).

cnf(c_1849,plain,
    ( k2_relat_1(sK5) = sK4
    | k2_relat_1(sK4) = X0
    | r2_hidden(sK0(sK4,X0),X0) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_1627])).

cnf(c_4167,plain,
    ( k2_relat_1(sK5) = sK4
    | k2_relat_1(sK4) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1627])).

cnf(c_174,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_189,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_175,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_731,plain,
    ( X0 != X1
    | k2_relat_1(sK5) != X1
    | k2_relat_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_1284,plain,
    ( X0 != k2_relat_1(sK5)
    | k2_relat_1(sK5) = X0
    | k2_relat_1(sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1286,plain,
    ( k2_relat_1(sK5) != k2_relat_1(sK5)
    | k2_relat_1(sK5) = sK4
    | sK4 != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_1285,plain,
    ( k2_relat_1(sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1596,plain,
    ( k2_relat_1(X0) != X1
    | sK4 != X1
    | sK4 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_1597,plain,
    ( k2_relat_1(sK4) != sK4
    | sK4 = k2_relat_1(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_609,plain,
    ( k2_relat_1(sK5) != X0
    | sK4 != X0
    | sK4 = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_3378,plain,
    ( k2_relat_1(sK5) != k2_relat_1(X0)
    | sK4 != k2_relat_1(X0)
    | sK4 = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_3383,plain,
    ( k2_relat_1(sK5) != k2_relat_1(sK4)
    | sK4 = k2_relat_1(sK5)
    | sK4 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3378])).

cnf(c_4168,plain,
    ( k2_relat_1(sK5) = k2_relat_1(sK4)
    | k2_relat_1(sK5) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1382])).

cnf(c_4304,plain,
    ( k2_relat_1(sK5) = sK4
    | v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4167,c_189,c_1286,c_1285,c_1597,c_3383,c_4168])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_416,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4814,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4459,c_416])).

cnf(c_4886,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4814])).

cnf(c_4889,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4800,c_1485,c_4304,c_4886])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,sK6),sK5)
    | k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_413,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    | r2_hidden(k4_tarski(X0,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_986,plain,
    ( k2_relat_1(sK5) != sK4
    | r2_hidden(k4_tarski(X0,sK6),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_705,c_413])).

cnf(c_4926,plain,
    ( sK4 != sK4
    | r2_hidden(k4_tarski(X0,sK6),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4889,c_986])).

cnf(c_4934,plain,
    ( r2_hidden(k4_tarski(X0,sK6),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4926])).

cnf(c_5279,plain,
    ( r2_hidden(sK6,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_4934])).

cnf(c_5280,plain,
    ( r2_hidden(sK6,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5279,c_4889])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK6,sK4)
    | k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    | r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_987,plain,
    ( k2_relat_1(sK5) != sK4
    | r2_hidden(sK6,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_705,c_412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5280,c_4889,c_987])).


%------------------------------------------------------------------------------
