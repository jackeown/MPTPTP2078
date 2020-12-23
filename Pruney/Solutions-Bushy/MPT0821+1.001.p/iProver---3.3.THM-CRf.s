%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:10 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   97 (1144 expanded)
%              Number of clauses        :   53 ( 338 expanded)
%              Number of leaves         :   13 ( 307 expanded)
%              Depth                    :   22
%              Number of atoms          :  295 (4730 expanded)
%              Number of equality atoms :  127 (1369 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X2,X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
     => r2_hidden(k4_tarski(X5,sK7(X5)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
          & r2_hidden(X3,X1) )
     => ( ! [X4] : ~ r2_hidden(k4_tarski(sK6,X4),X2)
        & r2_hidden(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k1_relset_1(sK4,sK3,sK5) != sK4
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK5)
            & r2_hidden(X3,sK4) ) )
      & ( k1_relset_1(sK4,sK3,sK5) = sK4
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK5)
            | ~ r2_hidden(X5,sK4) ) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k1_relset_1(sK4,sK3,sK5) != sK4
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK6,X4),sK5)
        & r2_hidden(sK6,sK4) ) )
    & ( k1_relset_1(sK4,sK3,sK5) = sK4
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK7(X5)),sK5)
          | ~ r2_hidden(X5,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f39,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k1_relset_1(sK4,sK3,sK5) = sK4
      | r2_hidden(k4_tarski(X5,sK7(X5)),sK5)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k1_relset_1(sK4,sK3,sK5) != sK4
      | ~ r2_hidden(k4_tarski(sK6,X4),sK5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,
    ( k1_relset_1(sK4,sK3,sK5) != sK4
    | r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_419,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_421,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_420,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1493,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_420])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_410,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_417,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_708,plain,
    ( k1_relset_1(sK4,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_410,c_417])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_418,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1065,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_418])).

cnf(c_13,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1462,plain,
    ( m1_subset_1(k1_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1065,c_13])).

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

cnf(c_1468,plain,
    ( m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_415])).

cnf(c_4254,plain,
    ( k1_relat_1(sK5) = X0
    | m1_subset_1(sK0(sK5,X0),sK4) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1468])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k4_tarski(X0,sK7(X0)),sK5)
    | k1_relset_1(sK4,sK3,sK5) = sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_411,plain,
    ( k1_relset_1(sK4,sK3,sK5) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7(X0)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_598,plain,
    ( k1_relset_1(sK4,sK3,sK5) = sK4
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_411,c_420])).

cnf(c_1022,plain,
    ( k1_relat_1(sK5) = sK4
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_708,c_598])).

cnf(c_1722,plain,
    ( k1_relat_1(sK5) = sK4
    | m1_subset_1(X0,sK4) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1468])).

cnf(c_4661,plain,
    ( k1_relat_1(sK5) = sK4
    | m1_subset_1(sK0(sK5,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4254,c_1722])).

cnf(c_1023,plain,
    ( k1_relat_1(sK5) = sK4
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK7(X0)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_708,c_411])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_422,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1521,plain,
    ( k1_relat_1(sK5) = X0
    | k1_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | r2_hidden(sK0(sK5,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_422])).

cnf(c_1540,plain,
    ( k1_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1521])).

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

cnf(c_1469,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_414])).

cnf(c_4253,plain,
    ( k1_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1469])).

cnf(c_4407,plain,
    ( k1_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4253])).

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

cnf(c_4676,plain,
    ( k1_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4254,c_416])).

cnf(c_4752,plain,
    ( k1_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4676])).

cnf(c_4755,plain,
    ( k1_relat_1(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4661,c_1540,c_4407,c_4752])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK6,X0),sK5)
    | k1_relset_1(sK4,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_413,plain,
    ( k1_relset_1(sK4,sK3,sK5) != sK4
    | r2_hidden(k4_tarski(sK6,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1024,plain,
    ( k1_relat_1(sK5) != sK4
    | r2_hidden(k4_tarski(sK6,X0),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_708,c_413])).

cnf(c_4792,plain,
    ( sK4 != sK4
    | r2_hidden(k4_tarski(sK6,X0),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4755,c_1024])).

cnf(c_4800,plain,
    ( r2_hidden(k4_tarski(sK6,X0),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4792])).

cnf(c_5154,plain,
    ( r2_hidden(sK6,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_4800])).

cnf(c_5155,plain,
    ( r2_hidden(sK6,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5154,c_4755])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK6,sK4)
    | k1_relset_1(sK4,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( k1_relset_1(sK4,sK3,sK5) != sK4
    | r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1025,plain,
    ( k1_relat_1(sK5) != sK4
    | r2_hidden(sK6,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_708,c_412])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5155,c_4755,c_1025])).


%------------------------------------------------------------------------------
