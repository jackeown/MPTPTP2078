%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:26 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 456 expanded)
%              Number of clauses        :   66 ( 139 expanded)
%              Number of leaves         :   16 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  354 (1842 expanded)
%              Number of equality atoms :  138 ( 492 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f17])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK6,sK5)
      | ~ r2_hidden(sK5,k1_relat_1(sK6)) )
    & ( k1_xboole_0 != k11_relat_1(sK6,sK5)
      | r2_hidden(sK5,k1_relat_1(sK6)) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f28])).

fof(f45,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f47,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_792,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_788,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_784,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_790,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1165,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_790])).

cnf(c_1254,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_1165])).

cnf(c_1596,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_1254])).

cnf(c_1721,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_788,c_1596])).

cnf(c_1727,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1721,c_1596])).

cnf(c_1974,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_1727])).

cnf(c_1984,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1974,c_7])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_310,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK6)
    | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_235])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_780,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1076,plain,
    ( r2_hidden(X0,k1_relat_1(k11_relat_1(sK6,X1))) != iProver_top
    | r2_hidden(k4_tarski(X1,k4_tarski(X0,sK4(k11_relat_1(sK6,X1),X0))),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_780])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_785,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2565,plain,
    ( r2_hidden(X0,k1_relat_1(k11_relat_1(sK6,X1))) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_785])).

cnf(c_2595,plain,
    ( k1_relat_1(k11_relat_1(sK6,X0)) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_2565])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_783,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3325,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0
    | k1_relat_1(k11_relat_1(sK6,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2595,c_783])).

cnf(c_902,plain,
    ( r2_hidden(sK1(k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_932,plain,
    ( r2_hidden(k4_tarski(sK5,sK1(k11_relat_1(sK6,sK5))),sK6)
    | ~ r2_hidden(sK1(k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_1060,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK1(k11_relat_1(sK6,sK5))),sK6)
    | r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_406,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1221,plain,
    ( k11_relat_1(sK6,sK5) = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_407,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1026,plain,
    ( X0 != X1
    | k11_relat_1(sK6,sK5) != X1
    | k11_relat_1(sK6,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_1804,plain,
    ( X0 != k11_relat_1(sK6,sK5)
    | k11_relat_1(sK6,sK5) = X0
    | k11_relat_1(sK6,sK5) != k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1805,plain,
    ( k11_relat_1(sK6,sK5) != k11_relat_1(sK6,sK5)
    | k11_relat_1(sK6,sK5) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1804])).

cnf(c_3376,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3325,c_14,c_902,c_932,c_1060,c_1221,c_1805])).

cnf(c_13,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_222,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_223,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_312,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK6)
    | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_223])).

cnf(c_313,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_781,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1077,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_781])).

cnf(c_3392,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_1077])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_421,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_911,plain,
    ( k11_relat_1(sK6,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_912,plain,
    ( k11_relat_1(sK6,sK5) != k1_xboole_0
    | k1_xboole_0 = k11_relat_1(sK6,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_950,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_951,plain,
    ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_977,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_978,plain,
    ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
    | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1384,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X1 != k11_relat_1(sK6,sK5)
    | X0 != sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_2254,plain,
    ( r2_hidden(sK4(sK6,sK5),X0)
    | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
    | X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2256,plain,
    ( X0 != k11_relat_1(sK6,sK5)
    | sK4(sK6,sK5) != sK4(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2254])).

cnf(c_2258,plain,
    ( sK4(sK6,sK5) != sK4(sK6,sK5)
    | k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_2255,plain,
    ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_3670,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3392,c_18,c_14,c_902,c_932,c_951,c_978,c_1060,c_2258,c_2255])).

cnf(c_3675,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3670,c_1727])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 2.16/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.00  
% 2.16/1.00  ------  iProver source info
% 2.16/1.00  
% 2.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.00  git: non_committed_changes: false
% 2.16/1.00  git: last_make_outside_of_git: false
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     num_symb
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 16
% 2.16/1.00  conjectures                             2
% 2.16/1.00  EPR                                     0
% 2.16/1.00  Horn                                    10
% 2.16/1.00  unary                                   1
% 2.16/1.00  binary                                  9
% 2.16/1.00  lits                                    38
% 2.16/1.00  lits eq                                 9
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 1
% 2.16/1.00  fd_pseudo_cond                          5
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status Theorem for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00   Resolution empty clause
% 2.16/1.00  
% 2.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  fof(f1,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f12,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.00    inference(nnf_transformation,[],[f1])).
% 2.16/1.00  
% 2.16/1.00  fof(f13,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.00    inference(flattening,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f14,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.00    inference(rectify,[],[f13])).
% 2.16/1.00  
% 2.16/1.00  fof(f15,plain,(
% 2.16/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f16,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 2.16/1.00  
% 2.16/1.00  fof(f33,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f16])).
% 2.16/1.00  
% 2.16/1.00  fof(f3,axiom,(
% 2.16/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f37,plain,(
% 2.16/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/1.00    inference(cnf_transformation,[],[f3])).
% 2.16/1.00  
% 2.16/1.00  fof(f50,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.16/1.00    inference(definition_unfolding,[],[f33,f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f2,axiom,(
% 2.16/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f9,plain,(
% 2.16/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.16/1.00    inference(ennf_transformation,[],[f2])).
% 2.16/1.00  
% 2.16/1.00  fof(f17,plain,(
% 2.16/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f18,plain,(
% 2.16/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f17])).
% 2.16/1.00  
% 2.16/1.00  fof(f36,plain,(
% 2.16/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.16/1.00    inference(cnf_transformation,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f5,axiom,(
% 2.16/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f19,plain,(
% 2.16/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.16/1.00    inference(nnf_transformation,[],[f5])).
% 2.16/1.00  
% 2.16/1.00  fof(f20,plain,(
% 2.16/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.16/1.00    inference(rectify,[],[f19])).
% 2.16/1.00  
% 2.16/1.00  fof(f23,plain,(
% 2.16/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f22,plain,(
% 2.16/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f21,plain,(
% 2.16/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f24,plain,(
% 2.16/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f39,plain,(
% 2.16/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f59,plain,(
% 2.16/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.16/1.00    inference(equality_resolution,[],[f39])).
% 2.16/1.00  
% 2.16/1.00  fof(f4,axiom,(
% 2.16/1.00    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f38,plain,(
% 2.16/1.00    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 2.16/1.00    inference(cnf_transformation,[],[f4])).
% 2.16/1.00  
% 2.16/1.00  fof(f54,plain,(
% 2.16/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 2.16/1.00    inference(definition_unfolding,[],[f38,f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f31,plain,(
% 2.16/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.16/1.00    inference(cnf_transformation,[],[f16])).
% 2.16/1.00  
% 2.16/1.00  fof(f52,plain,(
% 2.16/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.16/1.00    inference(definition_unfolding,[],[f31,f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f56,plain,(
% 2.16/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.16/1.00    inference(equality_resolution,[],[f52])).
% 2.16/1.00  
% 2.16/1.00  fof(f6,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f10,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.16/1.00    inference(ennf_transformation,[],[f6])).
% 2.16/1.00  
% 2.16/1.00  fof(f25,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.16/1.00    inference(nnf_transformation,[],[f10])).
% 2.16/1.00  
% 2.16/1.00  fof(f44,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f25])).
% 2.16/1.00  
% 2.16/1.00  fof(f7,conjecture,(
% 2.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.16/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f8,negated_conjecture,(
% 2.16/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.16/1.00    inference(negated_conjecture,[],[f7])).
% 2.16/1.00  
% 2.16/1.00  fof(f11,plain,(
% 2.16/1.00    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.16/1.00    inference(ennf_transformation,[],[f8])).
% 2.16/1.00  
% 2.16/1.00  fof(f26,plain,(
% 2.16/1.00    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.16/1.00    inference(nnf_transformation,[],[f11])).
% 2.16/1.00  
% 2.16/1.00  fof(f27,plain,(
% 2.16/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.16/1.00    inference(flattening,[],[f26])).
% 2.16/1.00  
% 2.16/1.00  fof(f28,plain,(
% 2.16/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f29,plain,(
% 2.16/1.00    (k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f28])).
% 2.16/1.00  
% 2.16/1.00  fof(f45,plain,(
% 2.16/1.00    v1_relat_1(sK6)),
% 2.16/1.00    inference(cnf_transformation,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f40,plain,(
% 2.16/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f58,plain,(
% 2.16/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f40])).
% 2.16/1.00  
% 2.16/1.00  fof(f47,plain,(
% 2.16/1.00    k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))),
% 2.16/1.00    inference(cnf_transformation,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f43,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f25])).
% 2.16/1.00  
% 2.16/1.00  fof(f46,plain,(
% 2.16/1.00    k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))),
% 2.16/1.00    inference(cnf_transformation,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2,plain,
% 2.16/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.16/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.16/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 2.16/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_792,plain,
% 2.16/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 2.16/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 2.16/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_6,plain,
% 2.16/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.16/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_788,plain,
% 2.16/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_11,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.16/1.00      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_784,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_7,plain,
% 2.16/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.16/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_4,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,X1)
% 2.16/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.16/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_790,plain,
% 2.16/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1165,plain,
% 2.16/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_7,c_790]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1254,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),k1_xboole_0) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_784,c_1165]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1596,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_784,c_1254]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1721,plain,
% 2.16/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_788,c_1596]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1727,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_1721,c_1596]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1974,plain,
% 2.16/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 2.16/1.00      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_792,c_1727]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1984,plain,
% 2.16/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 2.16/1.00      inference(demodulation,[status(thm)],[c_1974,c_7]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_12,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.16/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.16/1.00      | ~ v1_relat_1(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_16,negated_conjecture,
% 2.16/1.00      ( v1_relat_1(sK6) ),
% 2.16/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_234,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.16/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.16/1.00      | sK6 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_235,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_234]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_310,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(X1,X0),sK6) | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 2.16/1.00      inference(prop_impl,[status(thm)],[c_235]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_311,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_310]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_780,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1076,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(k11_relat_1(sK6,X1))) != iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X1,k4_tarski(X0,sK4(k11_relat_1(sK6,X1),X0))),sK6) = iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_784,c_780]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_10,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_785,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2565,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(k11_relat_1(sK6,X1))) != iProver_top
% 2.16/1.00      | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1076,c_785]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2595,plain,
% 2.16/1.00      ( k1_relat_1(k11_relat_1(sK6,X0)) = k1_xboole_0
% 2.16/1.00      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_1984,c_2565]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_14,negated_conjecture,
% 2.16/1.00      ( ~ r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_783,plain,
% 2.16/1.00      ( k1_xboole_0 = k11_relat_1(sK6,sK5)
% 2.16/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3325,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) = k1_xboole_0
% 2.16/1.00      | k1_relat_1(k11_relat_1(sK6,sK5)) = k1_xboole_0 ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_2595,c_783]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_902,plain,
% 2.16/1.00      ( r2_hidden(sK1(k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
% 2.16/1.00      | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_932,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(sK5,sK1(k11_relat_1(sK6,sK5))),sK6)
% 2.16/1.00      | ~ r2_hidden(sK1(k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1060,plain,
% 2.16/1.00      ( ~ r2_hidden(k4_tarski(sK5,sK1(k11_relat_1(sK6,sK5))),sK6)
% 2.16/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_406,plain,( X0 = X0 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1221,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) = k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_406]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_407,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1026,plain,
% 2.16/1.00      ( X0 != X1 | k11_relat_1(sK6,sK5) != X1 | k11_relat_1(sK6,sK5) = X0 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_407]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1804,plain,
% 2.16/1.00      ( X0 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | k11_relat_1(sK6,sK5) = X0
% 2.16/1.00      | k11_relat_1(sK6,sK5) != k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1026]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1805,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) != k11_relat_1(sK6,sK5)
% 2.16/1.00      | k11_relat_1(sK6,sK5) = k1_xboole_0
% 2.16/1.00      | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1804]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3376,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_3325,c_14,c_902,c_932,c_1060,c_1221,c_1805]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_13,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.16/1.00      | ~ v1_relat_1(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_222,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.16/1.00      | sK6 != X1 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_223,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_222]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_312,plain,
% 2.16/1.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK6) | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 2.16/1.00      inference(prop_impl,[status(thm)],[c_223]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_313,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_312]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_781,plain,
% 2.16/1.00      ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1077,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.16/1.00      | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_784,c_781]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3392,plain,
% 2.16/1.00      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
% 2.16/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.16/1.00      inference(superposition,[status(thm)],[c_3376,c_1077]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_15,negated_conjecture,
% 2.16/1.00      ( r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_18,plain,
% 2.16/1.00      ( k1_xboole_0 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_421,plain,
% 2.16/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_406]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_911,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) != X0
% 2.16/1.00      | k1_xboole_0 != X0
% 2.16/1.00      | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_407]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_912,plain,
% 2.16/1.00      ( k11_relat_1(sK6,sK5) != k1_xboole_0
% 2.16/1.00      | k1_xboole_0 = k11_relat_1(sK6,sK5)
% 2.16/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_911]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_950,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6)
% 2.16/1.00      | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_951,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) = iProver_top
% 2.16/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_977,plain,
% 2.16/1.00      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_313]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_978,plain,
% 2.16/1.00      ( r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) = iProver_top
% 2.16/1.00      | r2_hidden(k4_tarski(sK5,sK4(sK6,sK5)),sK6) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_410,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.16/1.00      theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1384,plain,
% 2.16/1.00      ( r2_hidden(X0,X1)
% 2.16/1.00      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.16/1.00      | X1 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | X0 != sK4(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_410]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2254,plain,
% 2.16/1.00      ( r2_hidden(sK4(sK6,sK5),X0)
% 2.16/1.00      | ~ r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5))
% 2.16/1.00      | X0 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | sK4(sK6,sK5) != sK4(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1384]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2256,plain,
% 2.16/1.00      ( X0 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | sK4(sK6,sK5) != sK4(sK6,sK5)
% 2.16/1.00      | r2_hidden(sK4(sK6,sK5),X0) = iProver_top
% 2.16/1.00      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2254]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2258,plain,
% 2.16/1.00      ( sK4(sK6,sK5) != sK4(sK6,sK5)
% 2.16/1.00      | k1_xboole_0 != k11_relat_1(sK6,sK5)
% 2.16/1.00      | r2_hidden(sK4(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
% 2.16/1.00      | r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2256]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2255,plain,
% 2.16/1.00      ( sK4(sK6,sK5) = sK4(sK6,sK5) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_406]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3670,plain,
% 2.16/1.00      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_3392,c_18,c_14,c_902,c_932,c_951,c_978,c_1060,c_2258,c_2255]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3675,plain,
% 2.16/1.00      ( $false ),
% 2.16/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3670,c_1727]) ).
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.01
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.008
% 2.16/1.00  total_time:                             0.148
% 2.16/1.00  num_of_symbols:                         46
% 2.16/1.00  num_of_terms:                           4189
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    33
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        0
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        0
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       82
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        2
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        1
% 2.16/1.00  pred_elim:                              1
% 2.16/1.00  pred_elim_cl:                           1
% 2.16/1.00  pred_elim_cycles:                       3
% 2.16/1.00  merged_defs:                            14
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          14
% 2.16/1.00  prep_cycles:                            4
% 2.16/1.00  pred_elim_time:                         0.001
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.001
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                16
% 2.16/1.00  conjectures:                            2
% 2.16/1.00  epr:                                    0
% 2.16/1.00  horn:                                   10
% 2.16/1.00  ground:                                 2
% 2.16/1.00  unary:                                  1
% 2.16/1.00  binary:                                 9
% 2.16/1.00  lits:                                   38
% 2.16/1.00  lits_eq:                                9
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                1
% 2.16/1.00  fd_pseudo_cond:                         5
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      28
% 2.16/1.00  prop_fast_solver_calls:                 482
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    1345
% 2.16/1.00  prop_preprocess_simplified:             4005
% 2.16/1.00  prop_fo_subsumed:                       2
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    342
% 2.16/1.00  inst_num_in_passive:                    67
% 2.16/1.00  inst_num_in_active:                     155
% 2.16/1.00  inst_num_in_unprocessed:                120
% 2.16/1.00  inst_num_of_loops:                      200
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          42
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      89
% 2.16/1.00  inst_num_of_non_proper_insts:           235
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.00  
% 2.16/1.00  ------ Resolution
% 2.16/1.00  
% 2.16/1.00  res_num_of_clauses:                     0
% 2.16/1.00  res_num_in_passive:                     0
% 2.16/1.00  res_num_in_active:                      0
% 2.16/1.00  res_num_of_loops:                       86
% 2.16/1.00  res_forward_subset_subsumed:            9
% 2.16/1.00  res_backward_subset_subsumed:           0
% 2.16/1.00  res_forward_subsumed:                   0
% 2.16/1.00  res_backward_subsumed:                  0
% 2.16/1.00  res_forward_subsumption_resolution:     0
% 2.16/1.00  res_backward_subsumption_resolution:    0
% 2.16/1.00  res_clause_to_clause_subsumption:       254
% 2.16/1.00  res_orphan_elimination:                 0
% 2.16/1.00  res_tautology_del:                      48
% 2.16/1.00  res_num_eq_res_simplified:              0
% 2.16/1.00  res_num_sel_changes:                    0
% 2.16/1.00  res_moves_from_active_to_pass:          0
% 2.16/1.00  
% 2.16/1.00  ------ Superposition
% 2.16/1.00  
% 2.16/1.00  sup_time_total:                         0.
% 2.16/1.00  sup_time_generating:                    0.
% 2.16/1.00  sup_time_sim_full:                      0.
% 2.16/1.00  sup_time_sim_immed:                     0.
% 2.16/1.00  
% 2.16/1.00  sup_num_of_clauses:                     97
% 2.16/1.00  sup_num_in_active:                      35
% 2.16/1.00  sup_num_in_passive:                     62
% 2.16/1.00  sup_num_of_loops:                       38
% 2.16/1.00  sup_fw_superposition:                   61
% 2.16/1.00  sup_bw_superposition:                   66
% 2.16/1.00  sup_immediate_simplified:               29
% 2.16/1.00  sup_given_eliminated:                   1
% 2.16/1.00  comparisons_done:                       0
% 2.16/1.00  comparisons_avoided:                    0
% 2.16/1.00  
% 2.16/1.00  ------ Simplifications
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  sim_fw_subset_subsumed:                 10
% 2.16/1.00  sim_bw_subset_subsumed:                 1
% 2.16/1.00  sim_fw_subsumed:                        14
% 2.16/1.00  sim_bw_subsumed:                        0
% 2.16/1.00  sim_fw_subsumption_res:                 1
% 2.16/1.00  sim_bw_subsumption_res:                 0
% 2.16/1.00  sim_tautology_del:                      8
% 2.16/1.00  sim_eq_tautology_del:                   4
% 2.16/1.00  sim_eq_res_simp:                        2
% 2.16/1.00  sim_fw_demodulated:                     5
% 2.16/1.00  sim_bw_demodulated:                     4
% 2.16/1.00  sim_light_normalised:                   2
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
