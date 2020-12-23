%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:29 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of clauses        :   35 (  46 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  249 ( 417 expanded)
%              Number of equality atoms :   64 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
     => ( ~ r1_xboole_0(k10_relat_1(X0,sK3),k10_relat_1(X0,sK4))
        & r1_xboole_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4))
    & r1_xboole_0(sK3,sK4)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f26,f25])).

fof(f45,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_669,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_659,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_662,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_661,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1047,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_661])).

cnf(c_2035,plain,
    ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_1047])).

cnf(c_2497,plain,
    ( k3_xboole_0(X0,X1) = k10_relat_1(X2,k1_xboole_0)
    | r2_hidden(sK0(X0,X1,k10_relat_1(X2,k1_xboole_0)),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_2035])).

cnf(c_10311,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_1047])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_663,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_945,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_662,c_663])).

cnf(c_10375,plain,
    ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10311,c_945])).

cnf(c_10430,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10375])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_654,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_946,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_654,c_663])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_653,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_656,plain,
    ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_890,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_656])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1902,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_19])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_664,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1906,plain,
    ( k10_relat_1(sK2,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_664])).

cnf(c_2847,plain,
    ( k10_relat_1(sK2,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_1906])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10430,c_2847,c_22,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:13:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.66/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/1.00  
% 3.66/1.00  ------  iProver source info
% 3.66/1.00  
% 3.66/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.66/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/1.00  git: non_committed_changes: false
% 3.66/1.00  git: last_make_outside_of_git: false
% 3.66/1.00  
% 3.66/1.00  ------ 
% 3.66/1.00  
% 3.66/1.00  ------ Input Options
% 3.66/1.00  
% 3.66/1.00  --out_options                           all
% 3.66/1.00  --tptp_safe_out                         true
% 3.66/1.00  --problem_path                          ""
% 3.66/1.00  --include_path                          ""
% 3.66/1.00  --clausifier                            res/vclausify_rel
% 3.66/1.00  --clausifier_options                    --mode clausify
% 3.66/1.00  --stdin                                 false
% 3.66/1.00  --stats_out                             sel
% 3.66/1.00  
% 3.66/1.00  ------ General Options
% 3.66/1.00  
% 3.66/1.00  --fof                                   false
% 3.66/1.00  --time_out_real                         604.99
% 3.66/1.00  --time_out_virtual                      -1.
% 3.66/1.00  --symbol_type_check                     false
% 3.66/1.00  --clausify_out                          false
% 3.66/1.00  --sig_cnt_out                           false
% 3.66/1.00  --trig_cnt_out                          false
% 3.66/1.00  --trig_cnt_out_tolerance                1.
% 3.66/1.00  --trig_cnt_out_sk_spl                   false
% 3.66/1.00  --abstr_cl_out                          false
% 3.66/1.00  
% 3.66/1.00  ------ Global Options
% 3.66/1.00  
% 3.66/1.00  --schedule                              none
% 3.66/1.00  --add_important_lit                     false
% 3.66/1.00  --prop_solver_per_cl                    1000
% 3.66/1.00  --min_unsat_core                        false
% 3.66/1.00  --soft_assumptions                      false
% 3.66/1.00  --soft_lemma_size                       3
% 3.66/1.00  --prop_impl_unit_size                   0
% 3.66/1.00  --prop_impl_unit                        []
% 3.66/1.00  --share_sel_clauses                     true
% 3.66/1.00  --reset_solvers                         false
% 3.66/1.00  --bc_imp_inh                            [conj_cone]
% 3.66/1.00  --conj_cone_tolerance                   3.
% 3.66/1.00  --extra_neg_conj                        none
% 3.66/1.00  --large_theory_mode                     true
% 3.66/1.00  --prolific_symb_bound                   200
% 3.66/1.00  --lt_threshold                          2000
% 3.66/1.00  --clause_weak_htbl                      true
% 3.66/1.00  --gc_record_bc_elim                     false
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing Options
% 3.66/1.00  
% 3.66/1.00  --preprocessing_flag                    true
% 3.66/1.00  --time_out_prep_mult                    0.1
% 3.66/1.00  --splitting_mode                        input
% 3.66/1.00  --splitting_grd                         true
% 3.66/1.00  --splitting_cvd                         false
% 3.66/1.00  --splitting_cvd_svl                     false
% 3.66/1.00  --splitting_nvd                         32
% 3.66/1.00  --sub_typing                            true
% 3.66/1.00  --prep_gs_sim                           false
% 3.66/1.00  --prep_unflatten                        true
% 3.66/1.00  --prep_res_sim                          true
% 3.66/1.00  --prep_upred                            true
% 3.66/1.00  --prep_sem_filter                       exhaustive
% 3.66/1.00  --prep_sem_filter_out                   false
% 3.66/1.00  --pred_elim                             false
% 3.66/1.00  --res_sim_input                         true
% 3.66/1.00  --eq_ax_congr_red                       true
% 3.66/1.00  --pure_diseq_elim                       true
% 3.66/1.00  --brand_transform                       false
% 3.66/1.00  --non_eq_to_eq                          false
% 3.66/1.00  --prep_def_merge                        true
% 3.66/1.00  --prep_def_merge_prop_impl              false
% 3.66/1.00  --prep_def_merge_mbd                    true
% 3.66/1.00  --prep_def_merge_tr_red                 false
% 3.66/1.00  --prep_def_merge_tr_cl                  false
% 3.66/1.00  --smt_preprocessing                     true
% 3.66/1.00  --smt_ac_axioms                         fast
% 3.66/1.00  --preprocessed_out                      false
% 3.66/1.00  --preprocessed_stats                    false
% 3.66/1.00  
% 3.66/1.00  ------ Abstraction refinement Options
% 3.66/1.00  
% 3.66/1.00  --abstr_ref                             []
% 3.66/1.00  --abstr_ref_prep                        false
% 3.66/1.00  --abstr_ref_until_sat                   false
% 3.66/1.00  --abstr_ref_sig_restrict                funpre
% 3.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.00  --abstr_ref_under                       []
% 3.66/1.00  
% 3.66/1.00  ------ SAT Options
% 3.66/1.00  
% 3.66/1.00  --sat_mode                              false
% 3.66/1.00  --sat_fm_restart_options                ""
% 3.66/1.00  --sat_gr_def                            false
% 3.66/1.00  --sat_epr_types                         true
% 3.66/1.00  --sat_non_cyclic_types                  false
% 3.66/1.00  --sat_finite_models                     false
% 3.66/1.00  --sat_fm_lemmas                         false
% 3.66/1.00  --sat_fm_prep                           false
% 3.66/1.00  --sat_fm_uc_incr                        true
% 3.66/1.00  --sat_out_model                         small
% 3.66/1.00  --sat_out_clauses                       false
% 3.66/1.00  
% 3.66/1.00  ------ QBF Options
% 3.66/1.00  
% 3.66/1.00  --qbf_mode                              false
% 3.66/1.00  --qbf_elim_univ                         false
% 3.66/1.00  --qbf_dom_inst                          none
% 3.66/1.00  --qbf_dom_pre_inst                      false
% 3.66/1.00  --qbf_sk_in                             false
% 3.66/1.00  --qbf_pred_elim                         true
% 3.66/1.00  --qbf_split                             512
% 3.66/1.00  
% 3.66/1.00  ------ BMC1 Options
% 3.66/1.00  
% 3.66/1.00  --bmc1_incremental                      false
% 3.66/1.00  --bmc1_axioms                           reachable_all
% 3.66/1.00  --bmc1_min_bound                        0
% 3.66/1.00  --bmc1_max_bound                        -1
% 3.66/1.00  --bmc1_max_bound_default                -1
% 3.66/1.00  --bmc1_symbol_reachability              true
% 3.66/1.00  --bmc1_property_lemmas                  false
% 3.66/1.00  --bmc1_k_induction                      false
% 3.66/1.00  --bmc1_non_equiv_states                 false
% 3.66/1.00  --bmc1_deadlock                         false
% 3.66/1.00  --bmc1_ucm                              false
% 3.66/1.00  --bmc1_add_unsat_core                   none
% 3.66/1.00  --bmc1_unsat_core_children              false
% 3.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.00  --bmc1_out_stat                         full
% 3.66/1.00  --bmc1_ground_init                      false
% 3.66/1.00  --bmc1_pre_inst_next_state              false
% 3.66/1.00  --bmc1_pre_inst_state                   false
% 3.66/1.00  --bmc1_pre_inst_reach_state             false
% 3.66/1.00  --bmc1_out_unsat_core                   false
% 3.66/1.00  --bmc1_aig_witness_out                  false
% 3.66/1.00  --bmc1_verbose                          false
% 3.66/1.00  --bmc1_dump_clauses_tptp                false
% 3.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.00  --bmc1_dump_file                        -
% 3.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.00  --bmc1_ucm_extend_mode                  1
% 3.66/1.00  --bmc1_ucm_init_mode                    2
% 3.66/1.00  --bmc1_ucm_cone_mode                    none
% 3.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.00  --bmc1_ucm_relax_model                  4
% 3.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.00  --bmc1_ucm_layered_model                none
% 3.66/1.00  --bmc1_ucm_max_lemma_size               10
% 3.66/1.00  
% 3.66/1.00  ------ AIG Options
% 3.66/1.00  
% 3.66/1.00  --aig_mode                              false
% 3.66/1.00  
% 3.66/1.00  ------ Instantiation Options
% 3.66/1.00  
% 3.66/1.00  --instantiation_flag                    true
% 3.66/1.00  --inst_sos_flag                         false
% 3.66/1.00  --inst_sos_phase                        true
% 3.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel_side                     num_symb
% 3.66/1.00  --inst_solver_per_active                1400
% 3.66/1.00  --inst_solver_calls_frac                1.
% 3.66/1.00  --inst_passive_queue_type               priority_queues
% 3.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.00  --inst_passive_queues_freq              [25;2]
% 3.66/1.00  --inst_dismatching                      true
% 3.66/1.00  --inst_eager_unprocessed_to_passive     true
% 3.66/1.00  --inst_prop_sim_given                   true
% 3.66/1.00  --inst_prop_sim_new                     false
% 3.66/1.00  --inst_subs_new                         false
% 3.66/1.00  --inst_eq_res_simp                      false
% 3.66/1.00  --inst_subs_given                       false
% 3.66/1.00  --inst_orphan_elimination               true
% 3.66/1.00  --inst_learning_loop_flag               true
% 3.66/1.00  --inst_learning_start                   3000
% 3.66/1.00  --inst_learning_factor                  2
% 3.66/1.00  --inst_start_prop_sim_after_learn       3
% 3.66/1.00  --inst_sel_renew                        solver
% 3.66/1.00  --inst_lit_activity_flag                true
% 3.66/1.00  --inst_restr_to_given                   false
% 3.66/1.00  --inst_activity_threshold               500
% 3.66/1.00  --inst_out_proof                        true
% 3.66/1.00  
% 3.66/1.00  ------ Resolution Options
% 3.66/1.00  
% 3.66/1.00  --resolution_flag                       true
% 3.66/1.00  --res_lit_sel                           adaptive
% 3.66/1.00  --res_lit_sel_side                      none
% 3.66/1.00  --res_ordering                          kbo
% 3.66/1.00  --res_to_prop_solver                    active
% 3.66/1.00  --res_prop_simpl_new                    false
% 3.66/1.00  --res_prop_simpl_given                  true
% 3.66/1.00  --res_passive_queue_type                priority_queues
% 3.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.00  --res_passive_queues_freq               [15;5]
% 3.66/1.00  --res_forward_subs                      full
% 3.66/1.00  --res_backward_subs                     full
% 3.66/1.00  --res_forward_subs_resolution           true
% 3.66/1.00  --res_backward_subs_resolution          true
% 3.66/1.00  --res_orphan_elimination                true
% 3.66/1.00  --res_time_limit                        2.
% 3.66/1.00  --res_out_proof                         true
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Options
% 3.66/1.00  
% 3.66/1.00  --superposition_flag                    true
% 3.66/1.00  --sup_passive_queue_type                priority_queues
% 3.66/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.00  --sup_passive_queues_freq               [1;4]
% 3.66/1.00  --demod_completeness_check              fast
% 3.66/1.00  --demod_use_ground                      true
% 3.66/1.00  --sup_to_prop_solver                    passive
% 3.66/1.00  --sup_prop_simpl_new                    true
% 3.66/1.00  --sup_prop_simpl_given                  true
% 3.66/1.00  --sup_fun_splitting                     false
% 3.66/1.00  --sup_smt_interval                      50000
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Simplification Setup
% 3.66/1.00  
% 3.66/1.00  --sup_indices_passive                   []
% 3.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_full_bw                           [BwDemod]
% 3.66/1.00  --sup_immed_triv                        [TrivRules]
% 3.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_immed_bw_main                     []
% 3.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  
% 3.66/1.00  ------ Combination Options
% 3.66/1.00  
% 3.66/1.00  --comb_res_mult                         3
% 3.66/1.00  --comb_sup_mult                         2
% 3.66/1.00  --comb_inst_mult                        10
% 3.66/1.00  
% 3.66/1.00  ------ Debug Options
% 3.66/1.00  
% 3.66/1.00  --dbg_backtrace                         false
% 3.66/1.00  --dbg_dump_prop_clauses                 false
% 3.66/1.00  --dbg_dump_prop_clauses_file            -
% 3.66/1.00  --dbg_out_stat                          false
% 3.66/1.00  ------ Parsing...
% 3.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/1.00  ------ Proving...
% 3.66/1.00  ------ Problem Properties 
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  clauses                                 19
% 3.66/1.00  conjectures                             4
% 3.66/1.00  EPR                                     4
% 3.66/1.00  Horn                                    17
% 3.66/1.00  unary                                   5
% 3.66/1.00  binary                                  5
% 3.66/1.00  lits                                    45
% 3.66/1.00  lits eq                                 6
% 3.66/1.00  fd_pure                                 0
% 3.66/1.00  fd_pseudo                               0
% 3.66/1.00  fd_cond                                 0
% 3.66/1.00  fd_pseudo_cond                          3
% 3.66/1.00  AC symbols                              0
% 3.66/1.00  
% 3.66/1.00  ------ Input Options Time Limit: Unbounded
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  ------ 
% 3.66/1.00  Current options:
% 3.66/1.00  ------ 
% 3.66/1.00  
% 3.66/1.00  ------ Input Options
% 3.66/1.00  
% 3.66/1.00  --out_options                           all
% 3.66/1.00  --tptp_safe_out                         true
% 3.66/1.00  --problem_path                          ""
% 3.66/1.00  --include_path                          ""
% 3.66/1.00  --clausifier                            res/vclausify_rel
% 3.66/1.00  --clausifier_options                    --mode clausify
% 3.66/1.00  --stdin                                 false
% 3.66/1.00  --stats_out                             sel
% 3.66/1.00  
% 3.66/1.00  ------ General Options
% 3.66/1.00  
% 3.66/1.00  --fof                                   false
% 3.66/1.00  --time_out_real                         604.99
% 3.66/1.00  --time_out_virtual                      -1.
% 3.66/1.00  --symbol_type_check                     false
% 3.66/1.00  --clausify_out                          false
% 3.66/1.00  --sig_cnt_out                           false
% 3.66/1.00  --trig_cnt_out                          false
% 3.66/1.00  --trig_cnt_out_tolerance                1.
% 3.66/1.00  --trig_cnt_out_sk_spl                   false
% 3.66/1.00  --abstr_cl_out                          false
% 3.66/1.00  
% 3.66/1.00  ------ Global Options
% 3.66/1.00  
% 3.66/1.00  --schedule                              none
% 3.66/1.00  --add_important_lit                     false
% 3.66/1.00  --prop_solver_per_cl                    1000
% 3.66/1.00  --min_unsat_core                        false
% 3.66/1.00  --soft_assumptions                      false
% 3.66/1.00  --soft_lemma_size                       3
% 3.66/1.00  --prop_impl_unit_size                   0
% 3.66/1.00  --prop_impl_unit                        []
% 3.66/1.00  --share_sel_clauses                     true
% 3.66/1.00  --reset_solvers                         false
% 3.66/1.00  --bc_imp_inh                            [conj_cone]
% 3.66/1.00  --conj_cone_tolerance                   3.
% 3.66/1.00  --extra_neg_conj                        none
% 3.66/1.00  --large_theory_mode                     true
% 3.66/1.00  --prolific_symb_bound                   200
% 3.66/1.00  --lt_threshold                          2000
% 3.66/1.00  --clause_weak_htbl                      true
% 3.66/1.00  --gc_record_bc_elim                     false
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing Options
% 3.66/1.00  
% 3.66/1.00  --preprocessing_flag                    true
% 3.66/1.00  --time_out_prep_mult                    0.1
% 3.66/1.00  --splitting_mode                        input
% 3.66/1.00  --splitting_grd                         true
% 3.66/1.00  --splitting_cvd                         false
% 3.66/1.00  --splitting_cvd_svl                     false
% 3.66/1.00  --splitting_nvd                         32
% 3.66/1.00  --sub_typing                            true
% 3.66/1.00  --prep_gs_sim                           false
% 3.66/1.00  --prep_unflatten                        true
% 3.66/1.00  --prep_res_sim                          true
% 3.66/1.00  --prep_upred                            true
% 3.66/1.00  --prep_sem_filter                       exhaustive
% 3.66/1.00  --prep_sem_filter_out                   false
% 3.66/1.00  --pred_elim                             false
% 3.66/1.00  --res_sim_input                         true
% 3.66/1.00  --eq_ax_congr_red                       true
% 3.66/1.00  --pure_diseq_elim                       true
% 3.66/1.00  --brand_transform                       false
% 3.66/1.00  --non_eq_to_eq                          false
% 3.66/1.00  --prep_def_merge                        true
% 3.66/1.00  --prep_def_merge_prop_impl              false
% 3.66/1.00  --prep_def_merge_mbd                    true
% 3.66/1.00  --prep_def_merge_tr_red                 false
% 3.66/1.00  --prep_def_merge_tr_cl                  false
% 3.66/1.00  --smt_preprocessing                     true
% 3.66/1.00  --smt_ac_axioms                         fast
% 3.66/1.00  --preprocessed_out                      false
% 3.66/1.00  --preprocessed_stats                    false
% 3.66/1.00  
% 3.66/1.00  ------ Abstraction refinement Options
% 3.66/1.00  
% 3.66/1.00  --abstr_ref                             []
% 3.66/1.00  --abstr_ref_prep                        false
% 3.66/1.00  --abstr_ref_until_sat                   false
% 3.66/1.00  --abstr_ref_sig_restrict                funpre
% 3.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.00  --abstr_ref_under                       []
% 3.66/1.00  
% 3.66/1.00  ------ SAT Options
% 3.66/1.00  
% 3.66/1.00  --sat_mode                              false
% 3.66/1.00  --sat_fm_restart_options                ""
% 3.66/1.00  --sat_gr_def                            false
% 3.66/1.00  --sat_epr_types                         true
% 3.66/1.00  --sat_non_cyclic_types                  false
% 3.66/1.00  --sat_finite_models                     false
% 3.66/1.00  --sat_fm_lemmas                         false
% 3.66/1.00  --sat_fm_prep                           false
% 3.66/1.00  --sat_fm_uc_incr                        true
% 3.66/1.00  --sat_out_model                         small
% 3.66/1.00  --sat_out_clauses                       false
% 3.66/1.00  
% 3.66/1.00  ------ QBF Options
% 3.66/1.00  
% 3.66/1.00  --qbf_mode                              false
% 3.66/1.00  --qbf_elim_univ                         false
% 3.66/1.00  --qbf_dom_inst                          none
% 3.66/1.00  --qbf_dom_pre_inst                      false
% 3.66/1.00  --qbf_sk_in                             false
% 3.66/1.00  --qbf_pred_elim                         true
% 3.66/1.00  --qbf_split                             512
% 3.66/1.00  
% 3.66/1.00  ------ BMC1 Options
% 3.66/1.00  
% 3.66/1.00  --bmc1_incremental                      false
% 3.66/1.00  --bmc1_axioms                           reachable_all
% 3.66/1.00  --bmc1_min_bound                        0
% 3.66/1.00  --bmc1_max_bound                        -1
% 3.66/1.00  --bmc1_max_bound_default                -1
% 3.66/1.00  --bmc1_symbol_reachability              true
% 3.66/1.00  --bmc1_property_lemmas                  false
% 3.66/1.00  --bmc1_k_induction                      false
% 3.66/1.00  --bmc1_non_equiv_states                 false
% 3.66/1.00  --bmc1_deadlock                         false
% 3.66/1.00  --bmc1_ucm                              false
% 3.66/1.00  --bmc1_add_unsat_core                   none
% 3.66/1.00  --bmc1_unsat_core_children              false
% 3.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.00  --bmc1_out_stat                         full
% 3.66/1.00  --bmc1_ground_init                      false
% 3.66/1.00  --bmc1_pre_inst_next_state              false
% 3.66/1.00  --bmc1_pre_inst_state                   false
% 3.66/1.00  --bmc1_pre_inst_reach_state             false
% 3.66/1.00  --bmc1_out_unsat_core                   false
% 3.66/1.00  --bmc1_aig_witness_out                  false
% 3.66/1.00  --bmc1_verbose                          false
% 3.66/1.00  --bmc1_dump_clauses_tptp                false
% 3.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.00  --bmc1_dump_file                        -
% 3.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.00  --bmc1_ucm_extend_mode                  1
% 3.66/1.00  --bmc1_ucm_init_mode                    2
% 3.66/1.00  --bmc1_ucm_cone_mode                    none
% 3.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.00  --bmc1_ucm_relax_model                  4
% 3.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.00  --bmc1_ucm_layered_model                none
% 3.66/1.00  --bmc1_ucm_max_lemma_size               10
% 3.66/1.00  
% 3.66/1.00  ------ AIG Options
% 3.66/1.00  
% 3.66/1.00  --aig_mode                              false
% 3.66/1.00  
% 3.66/1.00  ------ Instantiation Options
% 3.66/1.00  
% 3.66/1.00  --instantiation_flag                    true
% 3.66/1.00  --inst_sos_flag                         false
% 3.66/1.00  --inst_sos_phase                        true
% 3.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel_side                     num_symb
% 3.66/1.00  --inst_solver_per_active                1400
% 3.66/1.00  --inst_solver_calls_frac                1.
% 3.66/1.00  --inst_passive_queue_type               priority_queues
% 3.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.00  --inst_passive_queues_freq              [25;2]
% 3.66/1.00  --inst_dismatching                      true
% 3.66/1.00  --inst_eager_unprocessed_to_passive     true
% 3.66/1.00  --inst_prop_sim_given                   true
% 3.66/1.00  --inst_prop_sim_new                     false
% 3.66/1.00  --inst_subs_new                         false
% 3.66/1.00  --inst_eq_res_simp                      false
% 3.66/1.00  --inst_subs_given                       false
% 3.66/1.00  --inst_orphan_elimination               true
% 3.66/1.00  --inst_learning_loop_flag               true
% 3.66/1.00  --inst_learning_start                   3000
% 3.66/1.00  --inst_learning_factor                  2
% 3.66/1.00  --inst_start_prop_sim_after_learn       3
% 3.66/1.00  --inst_sel_renew                        solver
% 3.66/1.00  --inst_lit_activity_flag                true
% 3.66/1.00  --inst_restr_to_given                   false
% 3.66/1.00  --inst_activity_threshold               500
% 3.66/1.00  --inst_out_proof                        true
% 3.66/1.00  
% 3.66/1.00  ------ Resolution Options
% 3.66/1.00  
% 3.66/1.00  --resolution_flag                       true
% 3.66/1.00  --res_lit_sel                           adaptive
% 3.66/1.00  --res_lit_sel_side                      none
% 3.66/1.00  --res_ordering                          kbo
% 3.66/1.00  --res_to_prop_solver                    active
% 3.66/1.00  --res_prop_simpl_new                    false
% 3.66/1.00  --res_prop_simpl_given                  true
% 3.66/1.00  --res_passive_queue_type                priority_queues
% 3.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.00  --res_passive_queues_freq               [15;5]
% 3.66/1.00  --res_forward_subs                      full
% 3.66/1.00  --res_backward_subs                     full
% 3.66/1.00  --res_forward_subs_resolution           true
% 3.66/1.00  --res_backward_subs_resolution          true
% 3.66/1.00  --res_orphan_elimination                true
% 3.66/1.00  --res_time_limit                        2.
% 3.66/1.00  --res_out_proof                         true
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Options
% 3.66/1.00  
% 3.66/1.00  --superposition_flag                    true
% 3.66/1.00  --sup_passive_queue_type                priority_queues
% 3.66/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.00  --sup_passive_queues_freq               [1;4]
% 3.66/1.00  --demod_completeness_check              fast
% 3.66/1.00  --demod_use_ground                      true
% 3.66/1.00  --sup_to_prop_solver                    passive
% 3.66/1.00  --sup_prop_simpl_new                    true
% 3.66/1.00  --sup_prop_simpl_given                  true
% 3.66/1.00  --sup_fun_splitting                     false
% 3.66/1.00  --sup_smt_interval                      50000
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Simplification Setup
% 3.66/1.00  
% 3.66/1.00  --sup_indices_passive                   []
% 3.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_full_bw                           [BwDemod]
% 3.66/1.00  --sup_immed_triv                        [TrivRules]
% 3.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_immed_bw_main                     []
% 3.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  
% 3.66/1.00  ------ Combination Options
% 3.66/1.00  
% 3.66/1.00  --comb_res_mult                         3
% 3.66/1.00  --comb_sup_mult                         2
% 3.66/1.00  --comb_inst_mult                        10
% 3.66/1.00  
% 3.66/1.00  ------ Debug Options
% 3.66/1.00  
% 3.66/1.00  --dbg_backtrace                         false
% 3.66/1.00  --dbg_dump_prop_clauses                 false
% 3.66/1.00  --dbg_dump_prop_clauses_file            -
% 3.66/1.00  --dbg_out_stat                          false
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  ------ Proving...
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  % SZS status Theorem for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  fof(f1,axiom,(
% 3.66/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f15,plain,(
% 3.66/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.66/1.00    inference(nnf_transformation,[],[f1])).
% 3.66/1.00  
% 3.66/1.00  fof(f16,plain,(
% 3.66/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.66/1.00    inference(flattening,[],[f15])).
% 3.66/1.00  
% 3.66/1.00  fof(f17,plain,(
% 3.66/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.66/1.00    inference(rectify,[],[f16])).
% 3.66/1.00  
% 3.66/1.00  fof(f18,plain,(
% 3.66/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f19,plain,(
% 3.66/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.66/1.00  
% 3.66/1.00  fof(f32,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f19])).
% 3.66/1.00  
% 3.66/1.00  fof(f5,axiom,(
% 3.66/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f10,plain,(
% 3.66/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.66/1.00    inference(ennf_transformation,[],[f5])).
% 3.66/1.00  
% 3.66/1.00  fof(f21,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.66/1.00    inference(nnf_transformation,[],[f10])).
% 3.66/1.00  
% 3.66/1.00  fof(f22,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.66/1.00    inference(rectify,[],[f21])).
% 3.66/1.00  
% 3.66/1.00  fof(f23,plain,(
% 3.66/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f24,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 3.66/1.00  
% 3.66/1.00  fof(f40,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f24])).
% 3.66/1.00  
% 3.66/1.00  fof(f3,axiom,(
% 3.66/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f36,plain,(
% 3.66/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f3])).
% 3.66/1.00  
% 3.66/1.00  fof(f4,axiom,(
% 3.66/1.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f9,plain,(
% 3.66/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.66/1.00    inference(ennf_transformation,[],[f4])).
% 3.66/1.00  
% 3.66/1.00  fof(f37,plain,(
% 3.66/1.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f9])).
% 3.66/1.00  
% 3.66/1.00  fof(f2,axiom,(
% 3.66/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f20,plain,(
% 3.66/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.66/1.00    inference(nnf_transformation,[],[f2])).
% 3.66/1.00  
% 3.66/1.00  fof(f34,plain,(
% 3.66/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f20])).
% 3.66/1.00  
% 3.66/1.00  fof(f7,conjecture,(
% 3.66/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f8,negated_conjecture,(
% 3.66/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 3.66/1.00    inference(negated_conjecture,[],[f7])).
% 3.66/1.00  
% 3.66/1.00  fof(f13,plain,(
% 3.66/1.00    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f8])).
% 3.66/1.00  
% 3.66/1.00  fof(f14,plain,(
% 3.66/1.00    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.66/1.00    inference(flattening,[],[f13])).
% 3.66/1.00  
% 3.66/1.00  fof(f26,plain,(
% 3.66/1.00    ( ! [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(X0,sK3),k10_relat_1(X0,sK4)) & r1_xboole_0(sK3,sK4))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f25,plain,(
% 3.66/1.00    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK2,X1),k10_relat_1(sK2,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f27,plain,(
% 3.66/1.00    (~r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) & r1_xboole_0(sK3,sK4)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f26,f25])).
% 3.66/1.00  
% 3.66/1.00  fof(f45,plain,(
% 3.66/1.00    r1_xboole_0(sK3,sK4)),
% 3.66/1.00    inference(cnf_transformation,[],[f27])).
% 3.66/1.00  
% 3.66/1.00  fof(f44,plain,(
% 3.66/1.00    v1_funct_1(sK2)),
% 3.66/1.00    inference(cnf_transformation,[],[f27])).
% 3.66/1.00  
% 3.66/1.00  fof(f6,axiom,(
% 3.66/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f11,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.66/1.00    inference(ennf_transformation,[],[f6])).
% 3.66/1.00  
% 3.66/1.00  fof(f12,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.66/1.00    inference(flattening,[],[f11])).
% 3.66/1.00  
% 3.66/1.00  fof(f42,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f12])).
% 3.66/1.00  
% 3.66/1.00  fof(f43,plain,(
% 3.66/1.00    v1_relat_1(sK2)),
% 3.66/1.00    inference(cnf_transformation,[],[f27])).
% 3.66/1.00  
% 3.66/1.00  fof(f35,plain,(
% 3.66/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.66/1.00    inference(cnf_transformation,[],[f20])).
% 3.66/1.00  
% 3.66/1.00  fof(f46,plain,(
% 3.66/1.00    ~r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4))),
% 3.66/1.00    inference(cnf_transformation,[],[f27])).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1,plain,
% 3.66/1.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.66/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.66/1.00      | k3_xboole_0(X0,X1) = X2 ),
% 3.66/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_669,plain,
% 3.66/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.66/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.66/1.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_11,plain,
% 3.66/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.66/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.66/1.00      | ~ v1_relat_1(X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_659,plain,
% 3.66/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.66/1.00      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 3.66/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8,plain,
% 3.66/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.66/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_662,plain,
% 3.66/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_9,plain,
% 3.66/1.00      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_661,plain,
% 3.66/1.00      ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
% 3.66/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1047,plain,
% 3.66/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_662,c_661]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2035,plain,
% 3.66/1.00      ( r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) != iProver_top
% 3.66/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_659,c_1047]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2497,plain,
% 3.66/1.00      ( k3_xboole_0(X0,X1) = k10_relat_1(X2,k1_xboole_0)
% 3.66/1.00      | r2_hidden(sK0(X0,X1,k10_relat_1(X2,k1_xboole_0)),X1) = iProver_top
% 3.66/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_669,c_2035]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_10311,plain,
% 3.66/1.00      ( k10_relat_1(X0,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
% 3.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_2497,c_1047]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_7,plain,
% 3.66/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.66/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_663,plain,
% 3.66/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.66/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_945,plain,
% 3.66/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_662,c_663]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_10375,plain,
% 3.66/1.00      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.66/1.00      inference(demodulation,[status(thm)],[c_10311,c_945]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_10430,plain,
% 3.66/1.00      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0
% 3.66/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.66/1.00      inference(instantiation,[status(thm)],[c_10375]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_16,negated_conjecture,
% 3.66/1.00      ( r1_xboole_0(sK3,sK4) ),
% 3.66/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_654,plain,
% 3.66/1.00      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_946,plain,
% 3.66/1.00      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_654,c_663]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_17,negated_conjecture,
% 3.66/1.00      ( v1_funct_1(sK2) ),
% 3.66/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_653,plain,
% 3.66/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_14,plain,
% 3.66/1.00      ( ~ v1_funct_1(X0)
% 3.66/1.00      | ~ v1_relat_1(X0)
% 3.66/1.00      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_656,plain,
% 3.66/1.00      ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 3.66/1.00      | v1_funct_1(X0) != iProver_top
% 3.66/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_890,plain,
% 3.66/1.00      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
% 3.66/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_653,c_656]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_18,negated_conjecture,
% 3.66/1.00      ( v1_relat_1(sK2) ),
% 3.66/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_19,plain,
% 3.66/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1902,plain,
% 3.66/1.00      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_890,c_19]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_6,plain,
% 3.66/1.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.66/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_664,plain,
% 3.66/1.00      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 3.66/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1906,plain,
% 3.66/1.00      ( k10_relat_1(sK2,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.66/1.00      | r1_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1902,c_664]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2847,plain,
% 3.66/1.00      ( k10_relat_1(sK2,k1_xboole_0) != k1_xboole_0
% 3.66/1.00      | r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) = iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_946,c_1906]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_15,negated_conjecture,
% 3.66/1.00      ( ~ r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_22,plain,
% 3.66/1.00      ( r1_xboole_0(k10_relat_1(sK2,sK3),k10_relat_1(sK2,sK4)) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(contradiction,plain,
% 3.66/1.00      ( $false ),
% 3.66/1.00      inference(minisat,[status(thm)],[c_10430,c_2847,c_22,c_19]) ).
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  ------                               Statistics
% 3.66/1.00  
% 3.66/1.00  ------ Selected
% 3.66/1.00  
% 3.66/1.00  total_time:                             0.317
% 3.66/1.00  
%------------------------------------------------------------------------------
