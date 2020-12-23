%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0405+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:14 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   55 (  90 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 ( 347 expanded)
%              Number of equality atoms :   58 (  88 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,
    ( ? [X0] : ~ r1_setfam_1(k4_setfam_1(X0,X0),X0)
   => ~ r1_setfam_1(k4_setfam_1(sK6,sK6),sK6) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK6,sK6),sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f11,f20])).

fof(f34,plain,(
    ~ r1_setfam_1(k4_setfam_1(sK6,sK6),sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k6_subset_1(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k6_subset_1(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k6_subset_1(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k6_subset_1(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k6_subset_1(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k6_subset_1(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k6_subset_1(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k6_subset_1(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k6_subset_1(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k6_subset_1(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k6_subset_1(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k6_subset_1(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k6_subset_1(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k6_subset_1(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k6_subset_1(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k6_subset_1(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k4_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( k6_subset_1(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X8,X1] :
      ( k6_subset_1(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k4_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k4_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k4_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,negated_conjecture,
    ( ~ r1_setfam_1(k4_setfam_1(sK6,sK6),sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_170,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k4_setfam_1(sK6,sK6) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_171,plain,
    ( r2_hidden(sK0(k4_setfam_1(sK6,sK6),sK6),k4_setfam_1(sK6,sK6)) ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_456,plain,
    ( r2_hidden(sK0(k4_setfam_1(sK6,sK6),sK6),k4_setfam_1(sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k4_setfam_1(X1,X2))
    | k6_subset_1(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_459,plain,
    ( k6_subset_1(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k4_setfam_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_762,plain,
    ( k6_subset_1(sK4(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6)),sK5(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6))) = sK0(k4_setfam_1(sK6,sK6),sK6) ),
    inference(superposition,[status(thm)],[c_456,c_459])).

cnf(c_10,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_155,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X2,X3) != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_156,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | r1_setfam_1(X2,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_177,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | k4_setfam_1(sK6,sK6) != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r1_tarski(sK0(k4_setfam_1(sK6,sK6),sK6),X0) ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,sK6)
    | X0 != X1
    | sK0(k4_setfam_1(sK6,sK6),sK6) != k6_subset_1(X2,X3)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_156,c_178])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,sK6)
    | sK0(k4_setfam_1(sK6,sK6),sK6) != k6_subset_1(X1,X2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_455,plain,
    ( sK0(k4_setfam_1(sK6,sK6),sK6) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0)
    | r2_hidden(X2,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_780,plain,
    ( k1_zfmisc_1(sK4(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6))) != k1_zfmisc_1(X0)
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_455])).

cnf(c_909,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_780])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k4_setfam_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_543,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6)),sK6)
    | ~ r2_hidden(sK0(k4_setfam_1(sK6,sK6),sK6),k4_setfam_1(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_544,plain,
    ( r2_hidden(sK4(sK6,sK6,sK0(k4_setfam_1(sK6,sK6),sK6)),sK6) = iProver_top
    | r2_hidden(sK0(k4_setfam_1(sK6,sK6),sK6),k4_setfam_1(sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_172,plain,
    ( r2_hidden(sK0(k4_setfam_1(sK6,sK6),sK6),k4_setfam_1(sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_909,c_544,c_172])).


%------------------------------------------------------------------------------
