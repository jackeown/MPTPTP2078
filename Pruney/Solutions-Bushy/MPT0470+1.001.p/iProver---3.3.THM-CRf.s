%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0470+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:22 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 132 expanded)
%              Number of clauses        :   36 (  61 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   16
%              Number of atoms          :  228 ( 427 expanded)
%              Number of equality atoms :   70 ( 111 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
        & k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k5_relat_1(X0,k1_xboole_0) = k1_xboole_0
          & k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ( k5_relat_1(X0,k1_xboole_0) != k1_xboole_0
        | k5_relat_1(k1_xboole_0,X0) != k1_xboole_0 )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,
    ( ? [X0] :
        ( ( k5_relat_1(X0,k1_xboole_0) != k1_xboole_0
          | k5_relat_1(k1_xboole_0,X0) != k1_xboole_0 )
        & v1_relat_1(X0) )
   => ( ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
        | k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0 )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
      | k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0 )
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f17])).

fof(f28,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15,f14,f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,
    ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_125,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_124])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0_39,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_125])).

cnf(c_546,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_xboole_0,X0_40,k1_xboole_0),sK2(k1_xboole_0,X0_40,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_1322,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_xboole_0,sK4,k1_xboole_0),sK2(k1_xboole_0,sK4,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_513,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_1269,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_xboole_0,sK4,k1_xboole_0),sK1(k1_xboole_0,sK4,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_200,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_397,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_206,plain,
    ( r2_hidden(k4_tarski(sK2(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X1_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | ~ v1_relat_1(X2_40)
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40)
    | k5_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_392,plain,
    ( k5_relat_1(X0_40,X1_40) = X2_40
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X1_40) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40) = iProver_top
    | v1_relat_1(X2_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_399,plain,
    ( r2_hidden(X0_39,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_863,plain,
    ( k5_relat_1(X0_40,X1_40) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),X1_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_392,c_399])).

cnf(c_15,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_34,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_36,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1186,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),X1_40) = iProver_top
    | k5_relat_1(X0_40,X1_40) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_863,c_15,c_36])).

cnf(c_1187,plain,
    ( k5_relat_1(X0_40,X1_40) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),X1_40) = iProver_top
    | v1_relat_1(X1_40) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(renaming,[status(thm)],[c_1186])).

cnf(c_1194,plain,
    ( k5_relat_1(X0_40,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_399])).

cnf(c_1245,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | k5_relat_1(X0_40,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1194,c_15,c_36])).

cnf(c_1246,plain,
    ( k5_relat_1(X0_40,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_40) != iProver_top ),
    inference(renaming,[status(thm)],[c_1245])).

cnf(c_1251,plain,
    ( k5_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_397,c_1246])).

cnf(c_3,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_205,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK2(X0_40,X1_40,X2_40)),X0_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | ~ v1_relat_1(X2_40)
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40)
    | k5_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_512,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,k1_xboole_0),sK2(X0_40,X1_40,k1_xboole_0)),X0_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(X0_40,X1_40) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_545,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,X0_40,k1_xboole_0),sK2(k1_xboole_0,X0_40,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0_40,k1_xboole_0),sK1(k1_xboole_0,X0_40,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X0_40)
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(k1_xboole_0,X0_40) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_1181,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,sK4,k1_xboole_0),sK2(k1_xboole_0,sK4,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK0(k1_xboole_0,sK4,k1_xboole_0),sK1(k1_xboole_0,sK4,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_9,negated_conjecture,
    ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_201,negated_conjecture,
    ( k5_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,sK4) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_35,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1322,c_1269,c_1251,c_1181,c_201,c_35,c_7,c_10])).


%------------------------------------------------------------------------------
