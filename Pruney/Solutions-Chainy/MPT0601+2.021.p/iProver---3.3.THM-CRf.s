%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:22 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 215 expanded)
%              Number of clauses        :   48 (  81 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  270 ( 728 expanded)
%              Number of equality atoms :  109 ( 234 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK6,sK5)
        | ~ r2_hidden(sK5,k1_relat_1(sK6)) )
      & ( k1_xboole_0 != k11_relat_1(sK6,sK5)
        | r2_hidden(sK5,k1_relat_1(sK6)) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK6,sK5)
      | ~ r2_hidden(sK5,k1_relat_1(sK6)) )
    & ( k1_xboole_0 != k11_relat_1(sK6,sK5)
      | r2_hidden(sK5,k1_relat_1(sK6)) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).

fof(f64,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_800,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_799,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1510,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_799])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_68,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1519,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_68])).

cnf(c_1520,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1519])).

cnf(c_2156,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_1520])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_784,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3123,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,sK0(k1_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_784])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_788,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19280,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_788])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_782,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19806,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19280,c_782])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19996,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19806,c_23])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_787,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_783,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1576,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k11_relat_1(X1,X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_783])).

cnf(c_20014,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19996,c_1576])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_271,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_292,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_272,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1003,plain,
    ( k11_relat_1(sK6,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1004,plain,
    ( k11_relat_1(sK6,sK5) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK6,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1155,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1156,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_1171,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1172,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
    | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_6373,plain,
    ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1307,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X0 != sK4(sK6,sK5)
    | X1 != k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_19129,plain,
    ( r2_hidden(sK4(sK6,sK5),X0)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_19131,plain,
    ( X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19129])).

cnf(c_19133,plain,
    ( sK4(sK6,sK5) != sK4(sK6,sK5)
    | k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19131])).

cnf(c_20904,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20014,c_23,c_24,c_292,c_1004,c_1156,c_1172,c_6373,c_19133,c_19806])).

cnf(c_20909,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20904,c_1520])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.25/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/1.50  
% 7.25/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.50  
% 7.25/1.50  ------  iProver source info
% 7.25/1.50  
% 7.25/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.50  git: non_committed_changes: false
% 7.25/1.50  git: last_make_outside_of_git: false
% 7.25/1.50  
% 7.25/1.50  ------ 
% 7.25/1.50  ------ Parsing...
% 7.25/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.50  
% 7.25/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.25/1.50  
% 7.25/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.50  
% 7.25/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.50  ------ Proving...
% 7.25/1.50  ------ Problem Properties 
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  clauses                                 23
% 7.25/1.50  conjectures                             3
% 7.25/1.50  EPR                                     2
% 7.25/1.50  Horn                                    19
% 7.25/1.50  unary                                   4
% 7.25/1.50  binary                                  10
% 7.25/1.50  lits                                    51
% 7.25/1.50  lits eq                                 13
% 7.25/1.50  fd_pure                                 0
% 7.25/1.50  fd_pseudo                               0
% 7.25/1.50  fd_cond                                 0
% 7.25/1.50  fd_pseudo_cond                          5
% 7.25/1.50  AC symbols                              0
% 7.25/1.50  
% 7.25/1.50  ------ Input Options Time Limit: Unbounded
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  ------ 
% 7.25/1.50  Current options:
% 7.25/1.50  ------ 
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  ------ Proving...
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  % SZS status Theorem for theBenchmark.p
% 7.25/1.50  
% 7.25/1.50   Resolution empty clause
% 7.25/1.50  
% 7.25/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.50  
% 7.25/1.50  fof(f1,axiom,(
% 7.25/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f15,plain,(
% 7.25/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 7.25/1.50    inference(ennf_transformation,[],[f1])).
% 7.25/1.50  
% 7.25/1.50  fof(f21,plain,(
% 7.25/1.50    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 7.25/1.50    inference(nnf_transformation,[],[f15])).
% 7.25/1.50  
% 7.25/1.50  fof(f22,plain,(
% 7.25/1.50    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f23,plain,(
% 7.25/1.50    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 7.25/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 7.25/1.50  
% 7.25/1.50  fof(f41,plain,(
% 7.25/1.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.25/1.50    inference(cnf_transformation,[],[f23])).
% 7.25/1.50  
% 7.25/1.50  fof(f3,axiom,(
% 7.25/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f45,plain,(
% 7.25/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.25/1.50    inference(cnf_transformation,[],[f3])).
% 7.25/1.50  
% 7.25/1.50  fof(f2,axiom,(
% 7.25/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f14,plain,(
% 7.25/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.25/1.50    inference(rectify,[],[f2])).
% 7.25/1.50  
% 7.25/1.50  fof(f16,plain,(
% 7.25/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.25/1.50    inference(ennf_transformation,[],[f14])).
% 7.25/1.50  
% 7.25/1.50  fof(f24,plain,(
% 7.25/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f25,plain,(
% 7.25/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.25/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 7.25/1.50  
% 7.25/1.50  fof(f44,plain,(
% 7.25/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.25/1.50    inference(cnf_transformation,[],[f25])).
% 7.25/1.50  
% 7.25/1.50  fof(f4,axiom,(
% 7.25/1.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f46,plain,(
% 7.25/1.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.25/1.50    inference(cnf_transformation,[],[f4])).
% 7.25/1.50  
% 7.25/1.50  fof(f11,axiom,(
% 7.25/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f19,plain,(
% 7.25/1.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 7.25/1.50    inference(ennf_transformation,[],[f11])).
% 7.25/1.50  
% 7.25/1.50  fof(f36,plain,(
% 7.25/1.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 7.25/1.50    inference(nnf_transformation,[],[f19])).
% 7.25/1.50  
% 7.25/1.50  fof(f61,plain,(
% 7.25/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 7.25/1.50    inference(cnf_transformation,[],[f36])).
% 7.25/1.50  
% 7.25/1.50  fof(f9,axiom,(
% 7.25/1.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f29,plain,(
% 7.25/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.25/1.50    inference(nnf_transformation,[],[f9])).
% 7.25/1.50  
% 7.25/1.50  fof(f30,plain,(
% 7.25/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.25/1.50    inference(rectify,[],[f29])).
% 7.25/1.50  
% 7.25/1.50  fof(f33,plain,(
% 7.25/1.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f32,plain,(
% 7.25/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f31,plain,(
% 7.25/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f34,plain,(
% 7.25/1.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.25/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 7.25/1.50  
% 7.25/1.50  fof(f55,plain,(
% 7.25/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.25/1.50    inference(cnf_transformation,[],[f34])).
% 7.25/1.50  
% 7.25/1.50  fof(f70,plain,(
% 7.25/1.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.25/1.50    inference(equality_resolution,[],[f55])).
% 7.25/1.50  
% 7.25/1.50  fof(f12,conjecture,(
% 7.25/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.25/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.25/1.50  
% 7.25/1.50  fof(f13,negated_conjecture,(
% 7.25/1.50    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.25/1.50    inference(negated_conjecture,[],[f12])).
% 7.25/1.50  
% 7.25/1.50  fof(f20,plain,(
% 7.25/1.50    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.25/1.50    inference(ennf_transformation,[],[f13])).
% 7.25/1.50  
% 7.25/1.50  fof(f37,plain,(
% 7.25/1.50    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 7.25/1.50    inference(nnf_transformation,[],[f20])).
% 7.25/1.50  
% 7.25/1.50  fof(f38,plain,(
% 7.25/1.50    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.25/1.50    inference(flattening,[],[f37])).
% 7.25/1.50  
% 7.25/1.50  fof(f39,plain,(
% 7.25/1.50    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6))),
% 7.25/1.50    introduced(choice_axiom,[])).
% 7.25/1.50  
% 7.25/1.50  fof(f40,plain,(
% 7.25/1.50    (k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6)),
% 7.25/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f38,f39])).
% 7.25/1.50  
% 7.25/1.50  fof(f64,plain,(
% 7.25/1.50    k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))),
% 7.25/1.50    inference(cnf_transformation,[],[f40])).
% 7.25/1.50  
% 7.25/1.50  fof(f62,plain,(
% 7.25/1.50    v1_relat_1(sK6)),
% 7.25/1.50    inference(cnf_transformation,[],[f40])).
% 7.25/1.50  
% 7.25/1.50  fof(f54,plain,(
% 7.25/1.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.25/1.50    inference(cnf_transformation,[],[f34])).
% 7.25/1.50  
% 7.25/1.50  fof(f71,plain,(
% 7.25/1.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.25/1.50    inference(equality_resolution,[],[f54])).
% 7.25/1.50  
% 7.25/1.50  fof(f60,plain,(
% 7.25/1.50    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.25/1.50    inference(cnf_transformation,[],[f36])).
% 7.25/1.50  
% 7.25/1.50  fof(f63,plain,(
% 7.25/1.50    k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))),
% 7.25/1.50    inference(cnf_transformation,[],[f40])).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1,plain,
% 7.25/1.50      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 7.25/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_800,plain,
% 7.25/1.50      ( X0 = X1
% 7.25/1.50      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 7.25/1.50      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_4,plain,
% 7.25/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.25/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_2,plain,
% 7.25/1.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 7.25/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_799,plain,
% 7.25/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.25/1.50      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1510,plain,
% 7.25/1.50      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 7.25/1.50      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_4,c_799]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_5,plain,
% 7.25/1.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.25/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_68,plain,
% 7.25/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1519,plain,
% 7.25/1.50      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 7.25/1.50      inference(global_propositional_subsumption,[status(thm)],[c_1510,c_68]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1520,plain,
% 7.25/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.25/1.50      inference(renaming,[status(thm)],[c_1519]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_2156,plain,
% 7.25/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_800,c_1520]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_18,plain,
% 7.25/1.50      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 7.25/1.50      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.25/1.50      | ~ v1_relat_1(X1) ),
% 7.25/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_784,plain,
% 7.25/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 7.25/1.50      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 7.25/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_3123,plain,
% 7.25/1.50      ( k11_relat_1(X0,X1) = k1_xboole_0
% 7.25/1.50      | r2_hidden(k4_tarski(X1,sK0(k1_xboole_0,k11_relat_1(X0,X1))),X0) = iProver_top
% 7.25/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_2156,c_784]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_14,plain,
% 7.25/1.50      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.25/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_788,plain,
% 7.25/1.50      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.25/1.50      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19280,plain,
% 7.25/1.50      ( k11_relat_1(X0,X1) = k1_xboole_0
% 7.25/1.50      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 7.25/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_3123,c_788]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_20,negated_conjecture,
% 7.25/1.50      ( ~ r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 7.25/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_782,plain,
% 7.25/1.50      ( k1_xboole_0 = k11_relat_1(sK6,sK5)
% 7.25/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19806,plain,
% 7.25/1.50      ( k11_relat_1(sK6,sK5) = k1_xboole_0 | v1_relat_1(sK6) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_19280,c_782]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_22,negated_conjecture,
% 7.25/1.50      ( v1_relat_1(sK6) ),
% 7.25/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_23,plain,
% 7.25/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19996,plain,
% 7.25/1.50      ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
% 7.25/1.50      inference(global_propositional_subsumption,[status(thm)],[c_19806,c_23]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_15,plain,
% 7.25/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.25/1.50      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 7.25/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_787,plain,
% 7.25/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.25/1.50      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19,plain,
% 7.25/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.25/1.50      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.25/1.50      | ~ v1_relat_1(X1) ),
% 7.25/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_783,plain,
% 7.25/1.50      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 7.25/1.50      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 7.25/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1576,plain,
% 7.25/1.50      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.25/1.50      | r2_hidden(sK4(X1,X0),k11_relat_1(X1,X0)) = iProver_top
% 7.25/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_787,c_783]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_20014,plain,
% 7.25/1.50      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
% 7.25/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 7.25/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.25/1.50      inference(superposition,[status(thm)],[c_19996,c_1576]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_21,negated_conjecture,
% 7.25/1.50      ( r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
% 7.25/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_24,plain,
% 7.25/1.50      ( k1_xboole_0 != k11_relat_1(sK6,sK5)
% 7.25/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_271,plain,( X0 = X0 ),theory(equality) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_292,plain,
% 7.25/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_271]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_272,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1003,plain,
% 7.25/1.50      ( k11_relat_1(sK6,sK5) != X0
% 7.25/1.50      | k1_xboole_0 != X0
% 7.25/1.50      | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_272]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1004,plain,
% 7.25/1.50      ( k11_relat_1(sK6,sK5) != k1_xboole_0
% 7.25/1.50      | k1_xboole_0 = k11_relat_1(sK6,sK5)
% 7.25/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_1003]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1155,plain,
% 7.25/1.50      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
% 7.25/1.50      | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1156,plain,
% 7.25/1.50      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
% 7.25/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1171,plain,
% 7.25/1.50      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 7.25/1.50      | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
% 7.25/1.50      | ~ v1_relat_1(sK6) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1172,plain,
% 7.25/1.50      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
% 7.25/1.50      | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top
% 7.25/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_6373,plain,
% 7.25/1.50      ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_271]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_273,plain,
% 7.25/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.25/1.50      theory(equality) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_1307,plain,
% 7.25/1.50      ( r2_hidden(X0,X1)
% 7.25/1.50      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 7.25/1.50      | X0 != sK4(sK6,sK5)
% 7.25/1.50      | X1 != k11_relat_1(sK6,sK5) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_273]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19129,plain,
% 7.25/1.50      ( r2_hidden(sK4(sK6,sK5),X0)
% 7.25/1.50      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 7.25/1.50      | X0 != k11_relat_1(sK6,sK5)
% 7.25/1.50      | sK4(sK6,sK5) != sK4(sK6,sK5) ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_1307]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19131,plain,
% 7.25/1.50      ( X0 != k11_relat_1(sK6,sK5)
% 7.25/1.50      | sK4(sK6,sK5) != sK4(sK6,sK5)
% 7.25/1.50      | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
% 7.25/1.50      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
% 7.25/1.50      inference(predicate_to_equality,[status(thm)],[c_19129]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_19133,plain,
% 7.25/1.50      ( sK4(sK6,sK5) != sK4(sK6,sK5)
% 7.25/1.50      | k1_xboole_0 != k11_relat_1(sK6,sK5)
% 7.25/1.50      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
% 7.25/1.50      | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 7.25/1.50      inference(instantiation,[status(thm)],[c_19131]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_20904,plain,
% 7.25/1.50      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 7.25/1.50      inference(global_propositional_subsumption,
% 7.25/1.50                [status(thm)],
% 7.25/1.50                [c_20014,c_23,c_24,c_292,c_1004,c_1156,c_1172,c_6373,c_19133,
% 7.25/1.50                 c_19806]) ).
% 7.25/1.50  
% 7.25/1.50  cnf(c_20909,plain,
% 7.25/1.50      ( $false ),
% 7.25/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_20904,c_1520]) ).
% 7.25/1.50  
% 7.25/1.50  
% 7.25/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.50  
% 7.25/1.50  ------                               Statistics
% 7.25/1.50  
% 7.25/1.50  ------ Selected
% 7.25/1.50  
% 7.25/1.50  total_time:                             0.713
% 7.25/1.50  
%------------------------------------------------------------------------------
