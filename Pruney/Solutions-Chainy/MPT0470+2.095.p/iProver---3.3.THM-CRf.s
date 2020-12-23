%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:12 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 233 expanded)
%              Number of clauses        :   50 (  97 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  344 ( 828 expanded)
%              Number of equality atoms :  166 ( 311 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f28])).

fof(f46,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10636,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10643,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10638,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10639,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10804,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10638,c_10639])).

cnf(c_2,negated_conjecture,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10642,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11142,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
    | r1_tarski(X2,k4_xboole_0(X3,k1_tarski(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2))))) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10804,c_10642])).

cnf(c_11201,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10643,c_11142])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10641,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10726,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10641,c_10640])).

cnf(c_10732,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10636,c_10726])).

cnf(c_11204,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11201,c_10732])).

cnf(c_11205,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11204])).

cnf(c_11212,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11205,c_10639])).

cnf(c_11222,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0))))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11212,c_10642])).

cnf(c_11257,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10643,c_11222])).

cnf(c_11263,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11257,c_10732])).

cnf(c_11264,plain,
    ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11263])).

cnf(c_11269,plain,
    ( k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10636,c_11264])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10637,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10762,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10637,c_10639])).

cnf(c_10845,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r1_tarski(X2,k4_xboole_0(X3,k1_tarski(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2))))) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10762,c_10642])).

cnf(c_10912,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10643,c_10845])).

cnf(c_10917,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10912,c_10732])).

cnf(c_10918,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10917])).

cnf(c_10925,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10918,c_10639])).

cnf(c_10938,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,k4_xboole_0(X2,k1_tarski(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0))))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10925,c_10642])).

cnf(c_10971,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10643,c_10938])).

cnf(c_10977,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10971,c_10732])).

cnf(c_10978,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10977])).

cnf(c_10983,plain,
    ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10636,c_10978])).

cnf(c_249,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4614,plain,
    ( X0 != X1
    | X0 = k5_relat_1(X2,X3)
    | k5_relat_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_8561,plain,
    ( k5_relat_1(k1_xboole_0,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_4614])).

cnf(c_8562,plain,
    ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8561])).

cnf(c_2398,plain,
    ( X0 != X1
    | X0 = k5_relat_1(sK6,X2)
    | k5_relat_1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_2399,plain,
    ( k5_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_248,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_265,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11269,c_10983,c_8562,c_2399,c_265,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.54/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.01  
% 3.54/1.01  ------  iProver source info
% 3.54/1.01  
% 3.54/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.01  git: non_committed_changes: false
% 3.54/1.01  git: last_make_outside_of_git: false
% 3.54/1.01  
% 3.54/1.01  ------ 
% 3.54/1.01  ------ Parsing...
% 3.54/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  ------ Proving...
% 3.54/1.01  ------ Problem Properties 
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  clauses                                 18
% 3.54/1.01  conjectures                             3
% 3.54/1.01  EPR                                     2
% 3.54/1.01  Horn                                    14
% 3.54/1.01  unary                                   4
% 3.54/1.01  binary                                  2
% 3.54/1.01  lits                                    62
% 3.54/1.01  lits eq                                 6
% 3.54/1.01  fd_pure                                 0
% 3.54/1.01  fd_pseudo                               0
% 3.54/1.01  fd_cond                                 0
% 3.54/1.01  fd_pseudo_cond                          4
% 3.54/1.01  AC symbols                              0
% 3.54/1.01  
% 3.54/1.01  ------ Input Options Time Limit: Unbounded
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.54/1.01  Current options:
% 3.54/1.01  ------ 
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.54/1.01  
% 3.54/1.01  ------ Proving...
% 3.54/1.01  
% 3.54/1.01  
% 3.54/1.01  % SZS status Theorem for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.01  
% 3.54/1.01  fof(f8,conjecture,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f9,negated_conjecture,(
% 3.54/1.01    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.54/1.01    inference(negated_conjecture,[],[f8])).
% 3.54/1.01  
% 3.54/1.01  fof(f15,plain,(
% 3.54/1.01    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f9])).
% 3.54/1.01  
% 3.54/1.01  fof(f28,plain,(
% 3.54/1.01    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f29,plain,(
% 3.54/1.01    (k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6)),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f28])).
% 3.54/1.01  
% 3.54/1.01  fof(f46,plain,(
% 3.54/1.01    v1_relat_1(sK6)),
% 3.54/1.01    inference(cnf_transformation,[],[f29])).
% 3.54/1.01  
% 3.54/1.01  fof(f1,axiom,(
% 3.54/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f30,plain,(
% 3.54/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f1])).
% 3.54/1.01  
% 3.54/1.01  fof(f7,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f14,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f7])).
% 3.54/1.01  
% 3.54/1.01  fof(f22,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(nnf_transformation,[],[f14])).
% 3.54/1.01  
% 3.54/1.01  fof(f23,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(rectify,[],[f22])).
% 3.54/1.01  
% 3.54/1.01  fof(f26,plain,(
% 3.54/1.01    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f25,plain,(
% 3.54/1.01    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f24,plain,(
% 3.54/1.01    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f27,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f26,f25,f24])).
% 3.54/1.01  
% 3.54/1.01  fof(f44,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f27])).
% 3.54/1.01  
% 3.54/1.01  fof(f6,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f13,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f6])).
% 3.54/1.01  
% 3.54/1.01  fof(f18,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(nnf_transformation,[],[f13])).
% 3.54/1.01  
% 3.54/1.01  fof(f19,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(rectify,[],[f18])).
% 3.54/1.01  
% 3.54/1.01  fof(f20,plain,(
% 3.54/1.01    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)))),
% 3.54/1.01    introduced(choice_axiom,[])).
% 3.54/1.01  
% 3.54/1.01  fof(f21,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 3.54/1.01  
% 3.54/1.01  fof(f37,plain,(
% 3.54/1.01    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f21])).
% 3.54/1.01  
% 3.54/1.01  fof(f2,axiom,(
% 3.54/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f16,plain,(
% 3.54/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.54/1.01    inference(nnf_transformation,[],[f2])).
% 3.54/1.01  
% 3.54/1.01  fof(f17,plain,(
% 3.54/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.54/1.01    inference(flattening,[],[f16])).
% 3.54/1.01  
% 3.54/1.01  fof(f32,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f17])).
% 3.54/1.01  
% 3.54/1.01  fof(f48,plain,(
% 3.54/1.01    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.54/1.01    inference(equality_resolution,[],[f32])).
% 3.54/1.01  
% 3.54/1.01  fof(f3,axiom,(
% 3.54/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f34,plain,(
% 3.54/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.54/1.01    inference(cnf_transformation,[],[f3])).
% 3.54/1.01  
% 3.54/1.01  fof(f5,axiom,(
% 3.54/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.54/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.54/1.01  
% 3.54/1.01  fof(f12,plain,(
% 3.54/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.54/1.01    inference(ennf_transformation,[],[f5])).
% 3.54/1.01  
% 3.54/1.01  fof(f36,plain,(
% 3.54/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f12])).
% 3.54/1.01  
% 3.54/1.01  fof(f43,plain,(
% 3.54/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.54/1.01    inference(cnf_transformation,[],[f27])).
% 3.54/1.01  
% 3.54/1.01  fof(f47,plain,(
% 3.54/1.01    k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)),
% 3.54/1.01    inference(cnf_transformation,[],[f29])).
% 3.54/1.01  
% 3.54/1.01  cnf(c_17,negated_conjecture,
% 3.54/1.01      ( v1_relat_1(sK6) ),
% 3.54/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10636,plain,
% 3.54/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_0,plain,
% 3.54/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10643,plain,
% 3.54/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | ~ v1_relat_1(X1)
% 3.54/1.01      | ~ v1_relat_1(X2)
% 3.54/1.01      | k5_relat_1(X0,X1) = X2 ),
% 3.54/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10638,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_9,plain,
% 3.54/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.54/1.01      | r2_hidden(k4_tarski(X0,X1),X3)
% 3.54/1.01      | ~ r1_tarski(X2,X3)
% 3.54/1.01      | ~ v1_relat_1(X2) ),
% 3.54/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10639,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(X0,X1),X3) = iProver_top
% 3.54/1.01      | r1_tarski(X2,X3) != iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10804,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
% 3.54/1.01      | r1_tarski(X2,X3) != iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10638,c_10639]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2,negated_conjecture,
% 3.54/1.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
% 3.54/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10642,plain,
% 3.54/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11142,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) = iProver_top
% 3.54/1.01      | r1_tarski(X2,k4_xboole_0(X3,k1_tarski(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2))))) != iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10804,c_10642]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11201,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10643,c_11142]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4,plain,
% 3.54/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.54/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10641,plain,
% 3.54/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_6,plain,
% 3.54/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.54/1.01      | ~ v1_relat_1(X1)
% 3.54/1.01      | v1_relat_1(X0) ),
% 3.54/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10640,plain,
% 3.54/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10726,plain,
% 3.54/1.01      ( v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10641,c_10640]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10732,plain,
% 3.54/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10636,c_10726]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11204,plain,
% 3.54/1.01      ( v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.54/1.01      | k5_relat_1(X0,X1) = k1_xboole_0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_11201,c_10732]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11205,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X1) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_11204]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11212,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X2) = iProver_top
% 3.54/1.01      | r1_tarski(X1,X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_11205,c_10639]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11222,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(k4_tarski(sK4(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0))))) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_11212,c_10642]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11257,plain,
% 3.54/1.01      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10643,c_11222]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11263,plain,
% 3.54/1.01      ( v1_relat_1(X0) != iProver_top
% 3.54/1.01      | k5_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_11257,c_10732]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11264,plain,
% 3.54/1.01      ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.54/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_11263]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_11269,plain,
% 3.54/1.01      ( k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10636,c_11264]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_12,plain,
% 3.54/1.01      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 3.54/1.01      | ~ v1_relat_1(X0)
% 3.54/1.01      | ~ v1_relat_1(X1)
% 3.54/1.01      | ~ v1_relat_1(X2)
% 3.54/1.01      | k5_relat_1(X0,X1) = X2 ),
% 3.54/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10637,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10762,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
% 3.54/1.01      | r1_tarski(X2,X3) != iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10637,c_10639]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10845,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = X2
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.54/1.01      | r1_tarski(X2,k4_xboole_0(X3,k1_tarski(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2))))) != iProver_top
% 3.54/1.01      | v1_relat_1(X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10762,c_10642]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10912,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10643,c_10845]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10917,plain,
% 3.54/1.01      ( v1_relat_1(X1) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.54/1.01      | k5_relat_1(X0,X1) = k1_xboole_0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_10912,c_10732]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10918,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_10917]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10925,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2) = iProver_top
% 3.54/1.01      | r1_tarski(X0,X2) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10918,c_10639]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10938,plain,
% 3.54/1.01      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.54/1.01      | r1_tarski(X0,k4_xboole_0(X2,k1_tarski(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0))))) != iProver_top
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10925,c_10642]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10971,plain,
% 3.54/1.01      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.54/1.01      | v1_relat_1(X0) != iProver_top
% 3.54/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10643,c_10938]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10977,plain,
% 3.54/1.01      ( v1_relat_1(X0) != iProver_top
% 3.54/1.01      | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.54/1.01      inference(global_propositional_subsumption,
% 3.54/1.01                [status(thm)],
% 3.54/1.01                [c_10971,c_10732]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10978,plain,
% 3.54/1.01      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.54/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.54/1.01      inference(renaming,[status(thm)],[c_10977]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_10983,plain,
% 3.54/1.01      ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.54/1.01      inference(superposition,[status(thm)],[c_10636,c_10978]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_249,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_4614,plain,
% 3.54/1.01      ( X0 != X1 | X0 = k5_relat_1(X2,X3) | k5_relat_1(X2,X3) != X1 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_249]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_8561,plain,
% 3.54/1.01      ( k5_relat_1(k1_xboole_0,sK6) != X0
% 3.54/1.01      | k1_xboole_0 != X0
% 3.54/1.01      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6) ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_4614]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_8562,plain,
% 3.54/1.01      ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
% 3.54/1.01      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6)
% 3.54/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_8561]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2398,plain,
% 3.54/1.01      ( X0 != X1 | X0 = k5_relat_1(sK6,X2) | k5_relat_1(sK6,X2) != X1 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_249]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_2399,plain,
% 3.54/1.01      ( k5_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.54/1.01      | k1_xboole_0 = k5_relat_1(sK6,k1_xboole_0)
% 3.54/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_2398]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_248,plain,( X0 = X0 ),theory(equality) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_265,plain,
% 3.54/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.54/1.01      inference(instantiation,[status(thm)],[c_248]) ).
% 3.54/1.01  
% 3.54/1.01  cnf(c_16,negated_conjecture,
% 3.54/1.01      ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
% 3.54/1.02      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
% 3.54/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.54/1.02  
% 3.54/1.02  cnf(contradiction,plain,
% 3.54/1.02      ( $false ),
% 3.54/1.02      inference(minisat,
% 3.54/1.02                [status(thm)],
% 3.54/1.02                [c_11269,c_10983,c_8562,c_2399,c_265,c_16]) ).
% 3.54/1.02  
% 3.54/1.02  
% 3.54/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.02  
% 3.54/1.02  ------                               Statistics
% 3.54/1.02  
% 3.54/1.02  ------ Selected
% 3.54/1.02  
% 3.54/1.02  total_time:                             0.23
% 3.54/1.02  
%------------------------------------------------------------------------------
