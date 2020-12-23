%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0569+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:37 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 418 expanded)
%              Number of clauses        :   59 ( 147 expanded)
%              Number of leaves         :   12 (  90 expanded)
%              Depth                    :   25
%              Number of atoms          :  332 (1563 expanded)
%              Number of equality atoms :  136 ( 448 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f28])).

fof(f45,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f46,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_605,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_604,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK4(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_615,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_612,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1119,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_612])).

cnf(c_1262,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1119])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_606,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1546,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_606])).

cnf(c_3779,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_1546])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_613,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3780,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_1546])).

cnf(c_5717,plain,
    ( r1_xboole_0(X0,k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_3780])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_611,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5771,plain,
    ( k3_xboole_0(X0,k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5717,c_611])).

cnf(c_7084,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5771,c_6])).

cnf(c_8777,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3779,c_7084])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_609,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_607,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_602,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_874,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | k3_xboole_0(k2_relat_1(sK6),sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_602,c_611])).

cnf(c_1120,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_612])).

cnf(c_1544,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_606])).

cnf(c_2131,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK6),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_1544])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2675,plain,
    ( r2_hidden(sK3(X0,X1,sK6),sK5) != iProver_top
    | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_17])).

cnf(c_2676,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2675])).

cnf(c_2684,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_2676])).

cnf(c_2978,plain,
    ( r2_hidden(X0,k10_relat_1(sK6,sK5)) != iProver_top
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2684,c_17])).

cnf(c_2979,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0
    | r2_hidden(X0,k10_relat_1(sK6,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2978])).

cnf(c_8786,plain,
    ( k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8777,c_2979])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_610,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k2_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_614,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_694,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_610,c_614])).

cnf(c_3590,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_relat_1(X2)) != iProver_top
    | r2_hidden(sK2(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_694])).

cnf(c_10599,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8786,c_3590])).

cnf(c_11041,plain,
    ( r2_hidden(sK2(sK6,X0),k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10599,c_17])).

cnf(c_11042,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(sK6,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11041])).

cnf(c_11050,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11042,c_1546])).

cnf(c_11062,plain,
    ( r1_xboole_0(k2_relat_1(sK6),X0) = iProver_top
    | r2_hidden(sK4(k2_relat_1(sK6),X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_11050])).

cnf(c_13722,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_11062])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_603,plain,
    ( k1_xboole_0 != k10_relat_1(sK6,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8973,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8786,c_603])).

cnf(c_8974,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8973])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13722,c_8974])).


%------------------------------------------------------------------------------
