%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:13 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 296 expanded)
%              Number of clauses        :   29 ( 107 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  216 (1054 expanded)
%              Number of equality atoms :   72 ( 333 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f44,f47,f46,f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK7(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK9(X0)
        & r2_hidden(sK9(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK9(X0)
        & r2_hidden(sK9(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f23,f41])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK9(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f25,f50])).

fof(f82,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( r2_hidden(sK10(X0,X1),X1)
    | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1808,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK10(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1818,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2167,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1818])).

cnf(c_3469,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK10(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_2167])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK12(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1806,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK12(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1812,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3567,plain,
    ( r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1812,c_2167])).

cnf(c_22,plain,
    ( r2_hidden(sK9(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1810,plain,
    ( r2_hidden(sK9(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2417,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1810,c_2167])).

cnf(c_7573,plain,
    ( r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3567,c_2417])).

cnf(c_7588,plain,
    ( r2_hidden(X0,k1_relat_1(k10_relat_1(k1_xboole_0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1806,c_7573])).

cnf(c_10434,plain,
    ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3469,c_7588])).

cnf(c_10417,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3469,c_2167])).

cnf(c_10709,plain,
    ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10434,c_10417])).

cnf(c_8162,plain,
    ( r2_hidden(X0,k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1)),X2)) != iProver_top
    | v1_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1812,c_7588])).

cnf(c_8163,plain,
    ( v1_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1810,c_7588])).

cnf(c_8194,plain,
    ( r2_hidden(X0,k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1)),X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8162,c_8163])).

cnf(c_10435,plain,
    ( k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0)),X1) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3469,c_8194])).

cnf(c_10706,plain,
    ( k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0)),X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10435,c_10417])).

cnf(c_10710,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10709,c_10706])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_10992,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10710,c_30])).

cnf(c_11013,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10992])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.66/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.05  
% 2.66/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/1.05  
% 2.66/1.05  ------  iProver source info
% 2.66/1.05  
% 2.66/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.66/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/1.05  git: non_committed_changes: false
% 2.66/1.05  git: last_make_outside_of_git: false
% 2.66/1.05  
% 2.66/1.05  ------ 
% 2.66/1.05  
% 2.66/1.05  ------ Input Options
% 2.66/1.05  
% 2.66/1.05  --out_options                           all
% 2.66/1.05  --tptp_safe_out                         true
% 2.66/1.05  --problem_path                          ""
% 2.66/1.05  --include_path                          ""
% 2.66/1.05  --clausifier                            res/vclausify_rel
% 2.66/1.05  --clausifier_options                    --mode clausify
% 2.66/1.05  --stdin                                 false
% 2.66/1.05  --stats_out                             all
% 2.66/1.05  
% 2.66/1.05  ------ General Options
% 2.66/1.05  
% 2.66/1.05  --fof                                   false
% 2.66/1.05  --time_out_real                         305.
% 2.66/1.05  --time_out_virtual                      -1.
% 2.66/1.05  --symbol_type_check                     false
% 2.66/1.05  --clausify_out                          false
% 2.66/1.05  --sig_cnt_out                           false
% 2.66/1.05  --trig_cnt_out                          false
% 2.66/1.05  --trig_cnt_out_tolerance                1.
% 2.66/1.05  --trig_cnt_out_sk_spl                   false
% 2.66/1.05  --abstr_cl_out                          false
% 2.66/1.05  
% 2.66/1.05  ------ Global Options
% 2.66/1.05  
% 2.66/1.05  --schedule                              default
% 2.66/1.05  --add_important_lit                     false
% 2.66/1.05  --prop_solver_per_cl                    1000
% 2.66/1.05  --min_unsat_core                        false
% 2.66/1.05  --soft_assumptions                      false
% 2.66/1.05  --soft_lemma_size                       3
% 2.66/1.05  --prop_impl_unit_size                   0
% 2.66/1.05  --prop_impl_unit                        []
% 2.66/1.05  --share_sel_clauses                     true
% 2.66/1.05  --reset_solvers                         false
% 2.66/1.05  --bc_imp_inh                            [conj_cone]
% 2.66/1.05  --conj_cone_tolerance                   3.
% 2.66/1.05  --extra_neg_conj                        none
% 2.66/1.05  --large_theory_mode                     true
% 2.66/1.05  --prolific_symb_bound                   200
% 2.66/1.05  --lt_threshold                          2000
% 2.66/1.05  --clause_weak_htbl                      true
% 2.66/1.05  --gc_record_bc_elim                     false
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing Options
% 2.66/1.05  
% 2.66/1.05  --preprocessing_flag                    true
% 2.66/1.05  --time_out_prep_mult                    0.1
% 2.66/1.05  --splitting_mode                        input
% 2.66/1.05  --splitting_grd                         true
% 2.66/1.05  --splitting_cvd                         false
% 2.66/1.05  --splitting_cvd_svl                     false
% 2.66/1.05  --splitting_nvd                         32
% 2.66/1.05  --sub_typing                            true
% 2.66/1.05  --prep_gs_sim                           true
% 2.66/1.05  --prep_unflatten                        true
% 2.66/1.05  --prep_res_sim                          true
% 2.66/1.05  --prep_upred                            true
% 2.66/1.05  --prep_sem_filter                       exhaustive
% 2.66/1.05  --prep_sem_filter_out                   false
% 2.66/1.05  --pred_elim                             true
% 2.66/1.05  --res_sim_input                         true
% 2.66/1.05  --eq_ax_congr_red                       true
% 2.66/1.05  --pure_diseq_elim                       true
% 2.66/1.05  --brand_transform                       false
% 2.66/1.05  --non_eq_to_eq                          false
% 2.66/1.05  --prep_def_merge                        true
% 2.66/1.05  --prep_def_merge_prop_impl              false
% 2.66/1.05  --prep_def_merge_mbd                    true
% 2.66/1.05  --prep_def_merge_tr_red                 false
% 2.66/1.05  --prep_def_merge_tr_cl                  false
% 2.66/1.05  --smt_preprocessing                     true
% 2.66/1.05  --smt_ac_axioms                         fast
% 2.66/1.05  --preprocessed_out                      false
% 2.66/1.05  --preprocessed_stats                    false
% 2.66/1.05  
% 2.66/1.05  ------ Abstraction refinement Options
% 2.66/1.05  
% 2.66/1.05  --abstr_ref                             []
% 2.66/1.05  --abstr_ref_prep                        false
% 2.66/1.05  --abstr_ref_until_sat                   false
% 2.66/1.05  --abstr_ref_sig_restrict                funpre
% 2.66/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.05  --abstr_ref_under                       []
% 2.66/1.05  
% 2.66/1.05  ------ SAT Options
% 2.66/1.05  
% 2.66/1.05  --sat_mode                              false
% 2.66/1.05  --sat_fm_restart_options                ""
% 2.66/1.05  --sat_gr_def                            false
% 2.66/1.05  --sat_epr_types                         true
% 2.66/1.05  --sat_non_cyclic_types                  false
% 2.66/1.05  --sat_finite_models                     false
% 2.66/1.05  --sat_fm_lemmas                         false
% 2.66/1.05  --sat_fm_prep                           false
% 2.66/1.05  --sat_fm_uc_incr                        true
% 2.66/1.05  --sat_out_model                         small
% 2.66/1.05  --sat_out_clauses                       false
% 2.66/1.05  
% 2.66/1.05  ------ QBF Options
% 2.66/1.05  
% 2.66/1.05  --qbf_mode                              false
% 2.66/1.05  --qbf_elim_univ                         false
% 2.66/1.05  --qbf_dom_inst                          none
% 2.66/1.05  --qbf_dom_pre_inst                      false
% 2.66/1.05  --qbf_sk_in                             false
% 2.66/1.05  --qbf_pred_elim                         true
% 2.66/1.05  --qbf_split                             512
% 2.66/1.05  
% 2.66/1.05  ------ BMC1 Options
% 2.66/1.05  
% 2.66/1.05  --bmc1_incremental                      false
% 2.66/1.05  --bmc1_axioms                           reachable_all
% 2.66/1.05  --bmc1_min_bound                        0
% 2.66/1.05  --bmc1_max_bound                        -1
% 2.66/1.05  --bmc1_max_bound_default                -1
% 2.66/1.05  --bmc1_symbol_reachability              true
% 2.66/1.05  --bmc1_property_lemmas                  false
% 2.66/1.05  --bmc1_k_induction                      false
% 2.66/1.05  --bmc1_non_equiv_states                 false
% 2.66/1.05  --bmc1_deadlock                         false
% 2.66/1.05  --bmc1_ucm                              false
% 2.66/1.05  --bmc1_add_unsat_core                   none
% 2.66/1.05  --bmc1_unsat_core_children              false
% 2.66/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.05  --bmc1_out_stat                         full
% 2.66/1.05  --bmc1_ground_init                      false
% 2.66/1.05  --bmc1_pre_inst_next_state              false
% 2.66/1.05  --bmc1_pre_inst_state                   false
% 2.66/1.05  --bmc1_pre_inst_reach_state             false
% 2.66/1.05  --bmc1_out_unsat_core                   false
% 2.66/1.05  --bmc1_aig_witness_out                  false
% 2.66/1.05  --bmc1_verbose                          false
% 2.66/1.05  --bmc1_dump_clauses_tptp                false
% 2.66/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.05  --bmc1_dump_file                        -
% 2.66/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.05  --bmc1_ucm_extend_mode                  1
% 2.66/1.05  --bmc1_ucm_init_mode                    2
% 2.66/1.05  --bmc1_ucm_cone_mode                    none
% 2.66/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.05  --bmc1_ucm_relax_model                  4
% 2.66/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.05  --bmc1_ucm_layered_model                none
% 2.66/1.05  --bmc1_ucm_max_lemma_size               10
% 2.66/1.05  
% 2.66/1.05  ------ AIG Options
% 2.66/1.05  
% 2.66/1.05  --aig_mode                              false
% 2.66/1.05  
% 2.66/1.05  ------ Instantiation Options
% 2.66/1.05  
% 2.66/1.05  --instantiation_flag                    true
% 2.66/1.05  --inst_sos_flag                         false
% 2.66/1.05  --inst_sos_phase                        true
% 2.66/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.05  --inst_lit_sel_side                     num_symb
% 2.66/1.05  --inst_solver_per_active                1400
% 2.66/1.05  --inst_solver_calls_frac                1.
% 2.66/1.05  --inst_passive_queue_type               priority_queues
% 2.66/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.05  --inst_passive_queues_freq              [25;2]
% 2.66/1.05  --inst_dismatching                      true
% 2.66/1.05  --inst_eager_unprocessed_to_passive     true
% 2.66/1.05  --inst_prop_sim_given                   true
% 2.66/1.05  --inst_prop_sim_new                     false
% 2.66/1.05  --inst_subs_new                         false
% 2.66/1.05  --inst_eq_res_simp                      false
% 2.66/1.05  --inst_subs_given                       false
% 2.66/1.05  --inst_orphan_elimination               true
% 2.66/1.05  --inst_learning_loop_flag               true
% 2.66/1.05  --inst_learning_start                   3000
% 2.66/1.05  --inst_learning_factor                  2
% 2.66/1.05  --inst_start_prop_sim_after_learn       3
% 2.66/1.05  --inst_sel_renew                        solver
% 2.66/1.05  --inst_lit_activity_flag                true
% 2.66/1.05  --inst_restr_to_given                   false
% 2.66/1.05  --inst_activity_threshold               500
% 2.66/1.05  --inst_out_proof                        true
% 2.66/1.05  
% 2.66/1.05  ------ Resolution Options
% 2.66/1.05  
% 2.66/1.05  --resolution_flag                       true
% 2.66/1.05  --res_lit_sel                           adaptive
% 2.66/1.05  --res_lit_sel_side                      none
% 2.66/1.05  --res_ordering                          kbo
% 2.66/1.05  --res_to_prop_solver                    active
% 2.66/1.05  --res_prop_simpl_new                    false
% 2.66/1.05  --res_prop_simpl_given                  true
% 2.66/1.05  --res_passive_queue_type                priority_queues
% 2.66/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.05  --res_passive_queues_freq               [15;5]
% 2.66/1.05  --res_forward_subs                      full
% 2.66/1.05  --res_backward_subs                     full
% 2.66/1.05  --res_forward_subs_resolution           true
% 2.66/1.05  --res_backward_subs_resolution          true
% 2.66/1.05  --res_orphan_elimination                true
% 2.66/1.05  --res_time_limit                        2.
% 2.66/1.05  --res_out_proof                         true
% 2.66/1.05  
% 2.66/1.05  ------ Superposition Options
% 2.66/1.05  
% 2.66/1.05  --superposition_flag                    true
% 2.66/1.05  --sup_passive_queue_type                priority_queues
% 2.66/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.05  --demod_completeness_check              fast
% 2.66/1.05  --demod_use_ground                      true
% 2.66/1.05  --sup_to_prop_solver                    passive
% 2.66/1.05  --sup_prop_simpl_new                    true
% 2.66/1.05  --sup_prop_simpl_given                  true
% 2.66/1.05  --sup_fun_splitting                     false
% 2.66/1.05  --sup_smt_interval                      50000
% 2.66/1.05  
% 2.66/1.05  ------ Superposition Simplification Setup
% 2.66/1.05  
% 2.66/1.05  --sup_indices_passive                   []
% 2.66/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_full_bw                           [BwDemod]
% 2.66/1.05  --sup_immed_triv                        [TrivRules]
% 2.66/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_immed_bw_main                     []
% 2.66/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.05  
% 2.66/1.05  ------ Combination Options
% 2.66/1.05  
% 2.66/1.05  --comb_res_mult                         3
% 2.66/1.05  --comb_sup_mult                         2
% 2.66/1.05  --comb_inst_mult                        10
% 2.66/1.05  
% 2.66/1.05  ------ Debug Options
% 2.66/1.05  
% 2.66/1.05  --dbg_backtrace                         false
% 2.66/1.05  --dbg_dump_prop_clauses                 false
% 2.66/1.05  --dbg_dump_prop_clauses_file            -
% 2.66/1.05  --dbg_out_stat                          false
% 2.66/1.05  ------ Parsing...
% 2.66/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.05  ------ Proving...
% 2.66/1.05  ------ Problem Properties 
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  clauses                                 28
% 2.66/1.05  conjectures                             1
% 2.66/1.05  EPR                                     0
% 2.66/1.05  Horn                                    16
% 2.66/1.05  unary                                   3
% 2.66/1.05  binary                                  6
% 2.66/1.05  lits                                    93
% 2.66/1.05  lits eq                                 33
% 2.66/1.05  fd_pure                                 0
% 2.66/1.05  fd_pseudo                               0
% 2.66/1.05  fd_cond                                 0
% 2.66/1.05  fd_pseudo_cond                          13
% 2.66/1.05  AC symbols                              0
% 2.66/1.05  
% 2.66/1.05  ------ Schedule dynamic 5 is on 
% 2.66/1.05  
% 2.66/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  ------ 
% 2.66/1.05  Current options:
% 2.66/1.05  ------ 
% 2.66/1.05  
% 2.66/1.05  ------ Input Options
% 2.66/1.05  
% 2.66/1.05  --out_options                           all
% 2.66/1.05  --tptp_safe_out                         true
% 2.66/1.05  --problem_path                          ""
% 2.66/1.05  --include_path                          ""
% 2.66/1.05  --clausifier                            res/vclausify_rel
% 2.66/1.05  --clausifier_options                    --mode clausify
% 2.66/1.05  --stdin                                 false
% 2.66/1.05  --stats_out                             all
% 2.66/1.05  
% 2.66/1.05  ------ General Options
% 2.66/1.05  
% 2.66/1.05  --fof                                   false
% 2.66/1.05  --time_out_real                         305.
% 2.66/1.05  --time_out_virtual                      -1.
% 2.66/1.05  --symbol_type_check                     false
% 2.66/1.05  --clausify_out                          false
% 2.66/1.05  --sig_cnt_out                           false
% 2.66/1.05  --trig_cnt_out                          false
% 2.66/1.05  --trig_cnt_out_tolerance                1.
% 2.66/1.05  --trig_cnt_out_sk_spl                   false
% 2.66/1.05  --abstr_cl_out                          false
% 2.66/1.05  
% 2.66/1.05  ------ Global Options
% 2.66/1.05  
% 2.66/1.05  --schedule                              default
% 2.66/1.05  --add_important_lit                     false
% 2.66/1.05  --prop_solver_per_cl                    1000
% 2.66/1.05  --min_unsat_core                        false
% 2.66/1.05  --soft_assumptions                      false
% 2.66/1.05  --soft_lemma_size                       3
% 2.66/1.05  --prop_impl_unit_size                   0
% 2.66/1.05  --prop_impl_unit                        []
% 2.66/1.05  --share_sel_clauses                     true
% 2.66/1.05  --reset_solvers                         false
% 2.66/1.05  --bc_imp_inh                            [conj_cone]
% 2.66/1.05  --conj_cone_tolerance                   3.
% 2.66/1.05  --extra_neg_conj                        none
% 2.66/1.05  --large_theory_mode                     true
% 2.66/1.05  --prolific_symb_bound                   200
% 2.66/1.05  --lt_threshold                          2000
% 2.66/1.05  --clause_weak_htbl                      true
% 2.66/1.05  --gc_record_bc_elim                     false
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing Options
% 2.66/1.05  
% 2.66/1.05  --preprocessing_flag                    true
% 2.66/1.05  --time_out_prep_mult                    0.1
% 2.66/1.05  --splitting_mode                        input
% 2.66/1.05  --splitting_grd                         true
% 2.66/1.05  --splitting_cvd                         false
% 2.66/1.05  --splitting_cvd_svl                     false
% 2.66/1.05  --splitting_nvd                         32
% 2.66/1.05  --sub_typing                            true
% 2.66/1.05  --prep_gs_sim                           true
% 2.66/1.05  --prep_unflatten                        true
% 2.66/1.05  --prep_res_sim                          true
% 2.66/1.05  --prep_upred                            true
% 2.66/1.05  --prep_sem_filter                       exhaustive
% 2.66/1.05  --prep_sem_filter_out                   false
% 2.66/1.05  --pred_elim                             true
% 2.66/1.05  --res_sim_input                         true
% 2.66/1.05  --eq_ax_congr_red                       true
% 2.66/1.05  --pure_diseq_elim                       true
% 2.66/1.05  --brand_transform                       false
% 2.66/1.05  --non_eq_to_eq                          false
% 2.66/1.05  --prep_def_merge                        true
% 2.66/1.05  --prep_def_merge_prop_impl              false
% 2.66/1.05  --prep_def_merge_mbd                    true
% 2.66/1.05  --prep_def_merge_tr_red                 false
% 2.66/1.05  --prep_def_merge_tr_cl                  false
% 2.66/1.05  --smt_preprocessing                     true
% 2.66/1.05  --smt_ac_axioms                         fast
% 2.66/1.05  --preprocessed_out                      false
% 2.66/1.05  --preprocessed_stats                    false
% 2.66/1.05  
% 2.66/1.05  ------ Abstraction refinement Options
% 2.66/1.05  
% 2.66/1.05  --abstr_ref                             []
% 2.66/1.05  --abstr_ref_prep                        false
% 2.66/1.05  --abstr_ref_until_sat                   false
% 2.66/1.05  --abstr_ref_sig_restrict                funpre
% 2.66/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.05  --abstr_ref_under                       []
% 2.66/1.05  
% 2.66/1.05  ------ SAT Options
% 2.66/1.05  
% 2.66/1.05  --sat_mode                              false
% 2.66/1.05  --sat_fm_restart_options                ""
% 2.66/1.05  --sat_gr_def                            false
% 2.66/1.05  --sat_epr_types                         true
% 2.66/1.05  --sat_non_cyclic_types                  false
% 2.66/1.05  --sat_finite_models                     false
% 2.66/1.05  --sat_fm_lemmas                         false
% 2.66/1.05  --sat_fm_prep                           false
% 2.66/1.05  --sat_fm_uc_incr                        true
% 2.66/1.05  --sat_out_model                         small
% 2.66/1.05  --sat_out_clauses                       false
% 2.66/1.05  
% 2.66/1.05  ------ QBF Options
% 2.66/1.05  
% 2.66/1.05  --qbf_mode                              false
% 2.66/1.05  --qbf_elim_univ                         false
% 2.66/1.05  --qbf_dom_inst                          none
% 2.66/1.05  --qbf_dom_pre_inst                      false
% 2.66/1.05  --qbf_sk_in                             false
% 2.66/1.05  --qbf_pred_elim                         true
% 2.66/1.05  --qbf_split                             512
% 2.66/1.05  
% 2.66/1.05  ------ BMC1 Options
% 2.66/1.05  
% 2.66/1.05  --bmc1_incremental                      false
% 2.66/1.05  --bmc1_axioms                           reachable_all
% 2.66/1.05  --bmc1_min_bound                        0
% 2.66/1.05  --bmc1_max_bound                        -1
% 2.66/1.05  --bmc1_max_bound_default                -1
% 2.66/1.05  --bmc1_symbol_reachability              true
% 2.66/1.05  --bmc1_property_lemmas                  false
% 2.66/1.05  --bmc1_k_induction                      false
% 2.66/1.05  --bmc1_non_equiv_states                 false
% 2.66/1.05  --bmc1_deadlock                         false
% 2.66/1.05  --bmc1_ucm                              false
% 2.66/1.05  --bmc1_add_unsat_core                   none
% 2.66/1.05  --bmc1_unsat_core_children              false
% 2.66/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.05  --bmc1_out_stat                         full
% 2.66/1.05  --bmc1_ground_init                      false
% 2.66/1.05  --bmc1_pre_inst_next_state              false
% 2.66/1.05  --bmc1_pre_inst_state                   false
% 2.66/1.05  --bmc1_pre_inst_reach_state             false
% 2.66/1.05  --bmc1_out_unsat_core                   false
% 2.66/1.05  --bmc1_aig_witness_out                  false
% 2.66/1.05  --bmc1_verbose                          false
% 2.66/1.05  --bmc1_dump_clauses_tptp                false
% 2.66/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.05  --bmc1_dump_file                        -
% 2.66/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.05  --bmc1_ucm_extend_mode                  1
% 2.66/1.05  --bmc1_ucm_init_mode                    2
% 2.66/1.05  --bmc1_ucm_cone_mode                    none
% 2.66/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.05  --bmc1_ucm_relax_model                  4
% 2.66/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.05  --bmc1_ucm_layered_model                none
% 2.66/1.05  --bmc1_ucm_max_lemma_size               10
% 2.66/1.05  
% 2.66/1.05  ------ AIG Options
% 2.66/1.05  
% 2.66/1.05  --aig_mode                              false
% 2.66/1.05  
% 2.66/1.05  ------ Instantiation Options
% 2.66/1.05  
% 2.66/1.05  --instantiation_flag                    true
% 2.66/1.05  --inst_sos_flag                         false
% 2.66/1.05  --inst_sos_phase                        true
% 2.66/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.05  --inst_lit_sel_side                     none
% 2.66/1.05  --inst_solver_per_active                1400
% 2.66/1.05  --inst_solver_calls_frac                1.
% 2.66/1.05  --inst_passive_queue_type               priority_queues
% 2.66/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.05  --inst_passive_queues_freq              [25;2]
% 2.66/1.05  --inst_dismatching                      true
% 2.66/1.05  --inst_eager_unprocessed_to_passive     true
% 2.66/1.05  --inst_prop_sim_given                   true
% 2.66/1.05  --inst_prop_sim_new                     false
% 2.66/1.05  --inst_subs_new                         false
% 2.66/1.05  --inst_eq_res_simp                      false
% 2.66/1.05  --inst_subs_given                       false
% 2.66/1.05  --inst_orphan_elimination               true
% 2.66/1.05  --inst_learning_loop_flag               true
% 2.66/1.05  --inst_learning_start                   3000
% 2.66/1.05  --inst_learning_factor                  2
% 2.66/1.05  --inst_start_prop_sim_after_learn       3
% 2.66/1.05  --inst_sel_renew                        solver
% 2.66/1.05  --inst_lit_activity_flag                true
% 2.66/1.05  --inst_restr_to_given                   false
% 2.66/1.05  --inst_activity_threshold               500
% 2.66/1.05  --inst_out_proof                        true
% 2.66/1.05  
% 2.66/1.05  ------ Resolution Options
% 2.66/1.05  
% 2.66/1.05  --resolution_flag                       false
% 2.66/1.05  --res_lit_sel                           adaptive
% 2.66/1.05  --res_lit_sel_side                      none
% 2.66/1.05  --res_ordering                          kbo
% 2.66/1.05  --res_to_prop_solver                    active
% 2.66/1.05  --res_prop_simpl_new                    false
% 2.66/1.05  --res_prop_simpl_given                  true
% 2.66/1.05  --res_passive_queue_type                priority_queues
% 2.66/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.05  --res_passive_queues_freq               [15;5]
% 2.66/1.05  --res_forward_subs                      full
% 2.66/1.05  --res_backward_subs                     full
% 2.66/1.05  --res_forward_subs_resolution           true
% 2.66/1.05  --res_backward_subs_resolution          true
% 2.66/1.05  --res_orphan_elimination                true
% 2.66/1.05  --res_time_limit                        2.
% 2.66/1.05  --res_out_proof                         true
% 2.66/1.05  
% 2.66/1.05  ------ Superposition Options
% 2.66/1.05  
% 2.66/1.05  --superposition_flag                    true
% 2.66/1.05  --sup_passive_queue_type                priority_queues
% 2.66/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.05  --demod_completeness_check              fast
% 2.66/1.05  --demod_use_ground                      true
% 2.66/1.05  --sup_to_prop_solver                    passive
% 2.66/1.05  --sup_prop_simpl_new                    true
% 2.66/1.05  --sup_prop_simpl_given                  true
% 2.66/1.05  --sup_fun_splitting                     false
% 2.66/1.05  --sup_smt_interval                      50000
% 2.66/1.05  
% 2.66/1.05  ------ Superposition Simplification Setup
% 2.66/1.05  
% 2.66/1.05  --sup_indices_passive                   []
% 2.66/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_full_bw                           [BwDemod]
% 2.66/1.05  --sup_immed_triv                        [TrivRules]
% 2.66/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_immed_bw_main                     []
% 2.66/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.05  
% 2.66/1.05  ------ Combination Options
% 2.66/1.05  
% 2.66/1.05  --comb_res_mult                         3
% 2.66/1.05  --comb_sup_mult                         2
% 2.66/1.05  --comb_inst_mult                        10
% 2.66/1.05  
% 2.66/1.05  ------ Debug Options
% 2.66/1.05  
% 2.66/1.05  --dbg_backtrace                         false
% 2.66/1.05  --dbg_dump_prop_clauses                 false
% 2.66/1.05  --dbg_dump_prop_clauses_file            -
% 2.66/1.05  --dbg_out_stat                          false
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  ------ Proving...
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  % SZS status Theorem for theBenchmark.p
% 2.66/1.05  
% 2.66/1.05   Resolution empty clause
% 2.66/1.05  
% 2.66/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.05  
% 2.66/1.05  fof(f9,axiom,(
% 2.66/1.05    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f43,plain,(
% 2.66/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.66/1.05    inference(nnf_transformation,[],[f9])).
% 2.66/1.05  
% 2.66/1.05  fof(f44,plain,(
% 2.66/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.66/1.05    inference(rectify,[],[f43])).
% 2.66/1.05  
% 2.66/1.05  fof(f47,plain,(
% 2.66/1.05    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f46,plain,(
% 2.66/1.05    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK11(X0,X1)),X0))) )),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f45,plain,(
% 2.66/1.05    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f48,plain,(
% 2.66/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.66/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f44,f47,f46,f45])).
% 2.66/1.05  
% 2.66/1.05  fof(f77,plain,(
% 2.66/1.05    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)) )),
% 2.66/1.05    inference(cnf_transformation,[],[f48])).
% 2.66/1.05  
% 2.66/1.05  fof(f2,axiom,(
% 2.66/1.05    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f53,plain,(
% 2.66/1.05    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 2.66/1.05    inference(cnf_transformation,[],[f2])).
% 2.66/1.05  
% 2.66/1.05  fof(f5,axiom,(
% 2.66/1.05    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f32,plain,(
% 2.66/1.05    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.66/1.05    inference(nnf_transformation,[],[f5])).
% 2.66/1.05  
% 2.66/1.05  fof(f64,plain,(
% 2.66/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 2.66/1.05    inference(cnf_transformation,[],[f32])).
% 2.66/1.05  
% 2.66/1.05  fof(f75,plain,(
% 2.66/1.05    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.66/1.05    inference(cnf_transformation,[],[f48])).
% 2.66/1.05  
% 2.66/1.05  fof(f87,plain,(
% 2.66/1.05    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.66/1.05    inference(equality_resolution,[],[f75])).
% 2.66/1.05  
% 2.66/1.05  fof(f7,axiom,(
% 2.66/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f22,plain,(
% 2.66/1.05    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 2.66/1.05    inference(ennf_transformation,[],[f7])).
% 2.66/1.05  
% 2.66/1.05  fof(f35,plain,(
% 2.66/1.05    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.66/1.05    inference(nnf_transformation,[],[f22])).
% 2.66/1.05  
% 2.66/1.05  fof(f36,plain,(
% 2.66/1.05    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.66/1.05    inference(rectify,[],[f35])).
% 2.66/1.05  
% 2.66/1.05  fof(f39,plain,(
% 2.66/1.05    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)))),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f38,plain,(
% 2.66/1.05    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK7(X0,X1,X2)),X0)))) )),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f37,plain,(
% 2.66/1.05    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f40,plain,(
% 2.66/1.05    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X4),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.66/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).
% 2.66/1.05  
% 2.66/1.05  fof(f67,plain,(
% 2.66/1.05    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.66/1.05    inference(cnf_transformation,[],[f40])).
% 2.66/1.05  
% 2.66/1.05  fof(f85,plain,(
% 2.66/1.05    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(X6,sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.66/1.05    inference(equality_resolution,[],[f67])).
% 2.66/1.05  
% 2.66/1.05  fof(f8,axiom,(
% 2.66/1.05    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f15,plain,(
% 2.66/1.05    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 2.66/1.05    inference(unused_predicate_definition_removal,[],[f8])).
% 2.66/1.05  
% 2.66/1.05  fof(f23,plain,(
% 2.66/1.05    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.66/1.05    inference(ennf_transformation,[],[f15])).
% 2.66/1.05  
% 2.66/1.05  fof(f41,plain,(
% 2.66/1.05    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK9(X0) & r2_hidden(sK9(X0),X0)))),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f42,plain,(
% 2.66/1.05    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK9(X0) & r2_hidden(sK9(X0),X0)))),
% 2.66/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f23,f41])).
% 2.66/1.05  
% 2.66/1.05  fof(f73,plain,(
% 2.66/1.05    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK9(X0),X0)) )),
% 2.66/1.05    inference(cnf_transformation,[],[f42])).
% 2.66/1.05  
% 2.66/1.05  fof(f12,conjecture,(
% 2.66/1.05    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 2.66/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.05  
% 2.66/1.05  fof(f13,negated_conjecture,(
% 2.66/1.05    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 2.66/1.05    inference(negated_conjecture,[],[f12])).
% 2.66/1.05  
% 2.66/1.05  fof(f25,plain,(
% 2.66/1.05    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 2.66/1.05    inference(ennf_transformation,[],[f13])).
% 2.66/1.05  
% 2.66/1.05  fof(f50,plain,(
% 2.66/1.05    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13)),
% 2.66/1.05    introduced(choice_axiom,[])).
% 2.66/1.05  
% 2.66/1.05  fof(f51,plain,(
% 2.66/1.05    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13)),
% 2.66/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f25,f50])).
% 2.66/1.05  
% 2.66/1.05  fof(f82,plain,(
% 2.66/1.05    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13)),
% 2.66/1.05    inference(cnf_transformation,[],[f51])).
% 2.66/1.05  
% 2.66/1.05  cnf(c_24,plain,
% 2.66/1.05      ( r2_hidden(sK10(X0,X1),X1)
% 2.66/1.05      | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
% 2.66/1.05      | k1_relat_1(X0) = X1 ),
% 2.66/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1808,plain,
% 2.66/1.05      ( k1_relat_1(X0) = X1
% 2.66/1.05      | r2_hidden(sK10(X0,X1),X1) = iProver_top
% 2.66/1.05      | r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) = iProver_top ),
% 2.66/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1,plain,
% 2.66/1.05      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.66/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_13,plain,
% 2.66/1.05      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
% 2.66/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1818,plain,
% 2.66/1.05      ( k4_xboole_0(X0,k1_tarski(X1)) != X0 | r2_hidden(X1,X0) != iProver_top ),
% 2.66/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_2167,plain,
% 2.66/1.05      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1,c_1818]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_3469,plain,
% 2.66/1.05      ( k1_relat_1(k1_xboole_0) = X0
% 2.66/1.05      | r2_hidden(sK10(k1_xboole_0,X0),X0) = iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1808,c_2167]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_26,plain,
% 2.66/1.05      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.66/1.05      | r2_hidden(k4_tarski(X0,sK12(X1,X0)),X1) ),
% 2.66/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1806,plain,
% 2.66/1.05      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.66/1.05      | r2_hidden(k4_tarski(X0,sK12(X1,X0)),X1) = iProver_top ),
% 2.66/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_20,plain,
% 2.66/1.05      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.66/1.05      | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1)
% 2.66/1.05      | ~ v1_relat_1(X1) ),
% 2.66/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1812,plain,
% 2.66/1.05      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 2.66/1.05      | r2_hidden(k4_tarski(X0,sK8(X1,X2,X0)),X1) = iProver_top
% 2.66/1.05      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_3567,plain,
% 2.66/1.05      ( r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) != iProver_top
% 2.66/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1812,c_2167]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_22,plain,
% 2.66/1.05      ( r2_hidden(sK9(X0),X0) | v1_relat_1(X0) ),
% 2.66/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_1810,plain,
% 2.66/1.05      ( r2_hidden(sK9(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 2.66/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_2417,plain,
% 2.66/1.05      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1810,c_2167]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_7573,plain,
% 2.66/1.05      ( r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 2.66/1.05      inference(global_propositional_subsumption,[status(thm)],[c_3567,c_2417]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_7588,plain,
% 2.66/1.05      ( r2_hidden(X0,k1_relat_1(k10_relat_1(k1_xboole_0,X1))) != iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1806,c_7573]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10434,plain,
% 2.66/1.05      ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0) ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_3469,c_7588]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10417,plain,
% 2.66/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_3469,c_2167]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10709,plain,
% 2.66/1.05      ( k1_relat_1(k10_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.66/1.05      inference(light_normalisation,[status(thm)],[c_10434,c_10417]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_8162,plain,
% 2.66/1.05      ( r2_hidden(X0,k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1)),X2)) != iProver_top
% 2.66/1.05      | v1_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1))) != iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1812,c_7588]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_8163,plain,
% 2.66/1.05      ( v1_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0))) = iProver_top ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_1810,c_7588]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_8194,plain,
% 2.66/1.05      ( r2_hidden(X0,k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X1)),X2)) != iProver_top ),
% 2.66/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_8162,c_8163]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10435,plain,
% 2.66/1.05      ( k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0)),X1) = k1_relat_1(k1_xboole_0) ),
% 2.66/1.05      inference(superposition,[status(thm)],[c_3469,c_8194]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10706,plain,
% 2.66/1.05      ( k10_relat_1(k1_relat_1(k10_relat_1(k1_xboole_0,X0)),X1) = k1_xboole_0 ),
% 2.66/1.05      inference(light_normalisation,[status(thm)],[c_10435,c_10417]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10710,plain,
% 2.66/1.05      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.66/1.05      inference(demodulation,[status(thm)],[c_10709,c_10706]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_30,negated_conjecture,
% 2.66/1.05      ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK13) ),
% 2.66/1.05      inference(cnf_transformation,[],[f82]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_10992,plain,
% 2.66/1.05      ( k1_xboole_0 != k1_xboole_0 ),
% 2.66/1.05      inference(demodulation,[status(thm)],[c_10710,c_30]) ).
% 2.66/1.05  
% 2.66/1.05  cnf(c_11013,plain,
% 2.66/1.05      ( $false ),
% 2.66/1.05      inference(equality_resolution_simp,[status(thm)],[c_10992]) ).
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.05  
% 2.66/1.05  ------                               Statistics
% 2.66/1.05  
% 2.66/1.05  ------ General
% 2.66/1.05  
% 2.66/1.05  abstr_ref_over_cycles:                  0
% 2.66/1.05  abstr_ref_under_cycles:                 0
% 2.66/1.05  gc_basic_clause_elim:                   0
% 2.66/1.05  forced_gc_time:                         0
% 2.66/1.05  parsing_time:                           0.012
% 2.66/1.05  unif_index_cands_time:                  0.
% 2.66/1.05  unif_index_add_time:                    0.
% 2.66/1.05  orderings_time:                         0.
% 2.66/1.05  out_proof_time:                         0.008
% 2.66/1.05  total_time:                             0.339
% 2.66/1.05  num_of_symbols:                         57
% 2.66/1.05  num_of_terms:                           12000
% 2.66/1.05  
% 2.66/1.05  ------ Preprocessing
% 2.66/1.05  
% 2.66/1.05  num_of_splits:                          0
% 2.66/1.05  num_of_split_atoms:                     0
% 2.66/1.05  num_of_reused_defs:                     0
% 2.66/1.05  num_eq_ax_congr_red:                    92
% 2.66/1.05  num_of_sem_filtered_clauses:            1
% 2.66/1.05  num_of_subtypes:                        0
% 2.66/1.05  monotx_restored_types:                  0
% 2.66/1.05  sat_num_of_epr_types:                   0
% 2.66/1.05  sat_num_of_non_cyclic_types:            0
% 2.66/1.05  sat_guarded_non_collapsed_types:        0
% 2.66/1.05  num_pure_diseq_elim:                    0
% 2.66/1.05  simp_replaced_by:                       0
% 2.66/1.05  res_preprocessed:                       130
% 2.66/1.05  prep_upred:                             0
% 2.66/1.05  prep_unflattend:                        22
% 2.66/1.05  smt_new_axioms:                         0
% 2.66/1.05  pred_elim_cands:                        2
% 2.66/1.05  pred_elim:                              2
% 2.66/1.05  pred_elim_cl:                           3
% 2.66/1.05  pred_elim_cycles:                       4
% 2.66/1.05  merged_defs:                            10
% 2.66/1.05  merged_defs_ncl:                        0
% 2.66/1.05  bin_hyper_res:                          10
% 2.66/1.05  prep_cycles:                            4
% 2.66/1.05  pred_elim_time:                         0.015
% 2.66/1.05  splitting_time:                         0.
% 2.66/1.05  sem_filter_time:                        0.
% 2.66/1.05  monotx_time:                            0.001
% 2.66/1.05  subtype_inf_time:                       0.
% 2.66/1.05  
% 2.66/1.05  ------ Problem properties
% 2.66/1.05  
% 2.66/1.05  clauses:                                28
% 2.66/1.05  conjectures:                            1
% 2.66/1.05  epr:                                    0
% 2.66/1.05  horn:                                   16
% 2.66/1.05  ground:                                 1
% 2.66/1.05  unary:                                  3
% 2.66/1.05  binary:                                 6
% 2.66/1.05  lits:                                   93
% 2.66/1.05  lits_eq:                                33
% 2.66/1.05  fd_pure:                                0
% 2.66/1.05  fd_pseudo:                              0
% 2.66/1.05  fd_cond:                                0
% 2.66/1.05  fd_pseudo_cond:                         13
% 2.66/1.05  ac_symbols:                             0
% 2.66/1.05  
% 2.66/1.05  ------ Propositional Solver
% 2.66/1.05  
% 2.66/1.05  prop_solver_calls:                      26
% 2.66/1.05  prop_fast_solver_calls:                 1116
% 2.66/1.05  smt_solver_calls:                       0
% 2.66/1.05  smt_fast_solver_calls:                  0
% 2.66/1.05  prop_num_of_clauses:                    4164
% 2.66/1.05  prop_preprocess_simplified:             9610
% 2.66/1.05  prop_fo_subsumed:                       3
% 2.66/1.05  prop_solver_time:                       0.
% 2.66/1.05  smt_solver_time:                        0.
% 2.66/1.05  smt_fast_solver_time:                   0.
% 2.66/1.05  prop_fast_solver_time:                  0.
% 2.66/1.05  prop_unsat_core_time:                   0.
% 2.66/1.05  
% 2.66/1.05  ------ QBF
% 2.66/1.05  
% 2.66/1.05  qbf_q_res:                              0
% 2.66/1.05  qbf_num_tautologies:                    0
% 2.66/1.05  qbf_prep_cycles:                        0
% 2.66/1.05  
% 2.66/1.05  ------ BMC1
% 2.66/1.05  
% 2.66/1.05  bmc1_current_bound:                     -1
% 2.66/1.05  bmc1_last_solved_bound:                 -1
% 2.66/1.05  bmc1_unsat_core_size:                   -1
% 2.66/1.05  bmc1_unsat_core_parents_size:           -1
% 2.66/1.05  bmc1_merge_next_fun:                    0
% 2.66/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.05  
% 2.66/1.05  ------ Instantiation
% 2.66/1.05  
% 2.66/1.05  inst_num_of_clauses:                    929
% 2.66/1.05  inst_num_in_passive:                    355
% 2.66/1.05  inst_num_in_active:                     287
% 2.66/1.05  inst_num_in_unprocessed:                287
% 2.66/1.05  inst_num_of_loops:                      400
% 2.66/1.05  inst_num_of_learning_restarts:          0
% 2.66/1.05  inst_num_moves_active_passive:          113
% 2.66/1.05  inst_lit_activity:                      0
% 2.66/1.05  inst_lit_activity_moves:                0
% 2.66/1.05  inst_num_tautologies:                   0
% 2.66/1.05  inst_num_prop_implied:                  0
% 2.66/1.05  inst_num_existing_simplified:           0
% 2.66/1.05  inst_num_eq_res_simplified:             0
% 2.66/1.05  inst_num_child_elim:                    0
% 2.66/1.05  inst_num_of_dismatching_blockings:      412
% 2.66/1.05  inst_num_of_non_proper_insts:           554
% 2.66/1.05  inst_num_of_duplicates:                 0
% 2.66/1.05  inst_inst_num_from_inst_to_res:         0
% 2.66/1.05  inst_dismatching_checking_time:         0.
% 2.66/1.05  
% 2.66/1.05  ------ Resolution
% 2.66/1.05  
% 2.66/1.05  res_num_of_clauses:                     0
% 2.66/1.05  res_num_in_passive:                     0
% 2.66/1.05  res_num_in_active:                      0
% 2.66/1.05  res_num_of_loops:                       134
% 2.66/1.05  res_forward_subset_subsumed:            37
% 2.66/1.05  res_backward_subset_subsumed:           0
% 2.66/1.05  res_forward_subsumed:                   0
% 2.66/1.05  res_backward_subsumed:                  0
% 2.66/1.05  res_forward_subsumption_resolution:     0
% 2.66/1.05  res_backward_subsumption_resolution:    0
% 2.66/1.05  res_clause_to_clause_subsumption:       608
% 2.66/1.05  res_orphan_elimination:                 0
% 2.66/1.05  res_tautology_del:                      39
% 2.66/1.05  res_num_eq_res_simplified:              0
% 2.66/1.05  res_num_sel_changes:                    0
% 2.66/1.05  res_moves_from_active_to_pass:          0
% 2.66/1.05  
% 2.66/1.05  ------ Superposition
% 2.66/1.05  
% 2.66/1.05  sup_time_total:                         0.
% 2.66/1.05  sup_time_generating:                    0.
% 2.66/1.05  sup_time_sim_full:                      0.
% 2.66/1.05  sup_time_sim_immed:                     0.
% 2.66/1.05  
% 2.66/1.05  sup_num_of_clauses:                     251
% 2.66/1.05  sup_num_in_active:                      32
% 2.66/1.05  sup_num_in_passive:                     219
% 2.66/1.05  sup_num_of_loops:                       78
% 2.66/1.05  sup_fw_superposition:                   210
% 2.66/1.05  sup_bw_superposition:                   94
% 2.66/1.05  sup_immediate_simplified:               98
% 2.66/1.05  sup_given_eliminated:                   1
% 2.66/1.05  comparisons_done:                       0
% 2.66/1.05  comparisons_avoided:                    0
% 2.66/1.05  
% 2.66/1.05  ------ Simplifications
% 2.66/1.05  
% 2.66/1.05  
% 2.66/1.05  sim_fw_subset_subsumed:                 5
% 2.66/1.05  sim_bw_subset_subsumed:                 0
% 2.66/1.05  sim_fw_subsumed:                        4
% 2.66/1.05  sim_bw_subsumed:                        0
% 2.66/1.05  sim_fw_subsumption_res:                 60
% 2.66/1.05  sim_bw_subsumption_res:                 0
% 2.66/1.05  sim_tautology_del:                      5
% 2.66/1.05  sim_eq_tautology_del:                   17
% 2.66/1.05  sim_eq_res_simp:                        0
% 2.66/1.05  sim_fw_demodulated:                     1
% 2.66/1.05  sim_bw_demodulated:                     62
% 2.66/1.05  sim_light_normalised:                   36
% 2.66/1.05  sim_joinable_taut:                      0
% 2.66/1.05  sim_joinable_simp:                      0
% 2.66/1.05  sim_ac_normalised:                      0
% 2.66/1.05  sim_smt_subsumption:                    0
% 2.66/1.05  
%------------------------------------------------------------------------------
