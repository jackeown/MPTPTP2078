%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:25 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 565 expanded)
%              Number of clauses        :   67 ( 162 expanded)
%              Number of leaves         :   15 ( 154 expanded)
%              Depth                    :   22
%              Number of atoms          :  341 (2301 expanded)
%              Number of equality atoms :  136 ( 653 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f1])).

fof(f10,plain,(
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

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f11])).

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

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | ~ r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | sK1(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_940,plain,
    ( sK1(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_943,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_247,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_374,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK6)
    | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_248])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_930,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1564,plain,
    ( r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK6,X0),X1)),sK6) = iProver_top
    | r1_xboole_0(k11_relat_1(sK6,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_943,c_930])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_935,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3923,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r1_xboole_0(k11_relat_1(sK6,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1564,c_935])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_939,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_945,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2185,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_945])).

cnf(c_4317,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3923,c_2185])).

cnf(c_5020,plain,
    ( sK1(X0,k11_relat_1(sK6,X1)) = X0
    | k2_tarski(X0,X0) = k11_relat_1(sK6,X1)
    | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_4317])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_933,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_29810,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0
    | sK1(X0,k11_relat_1(sK6,sK5)) = X0
    | k2_tarski(X0,X0) = k11_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_5020,c_933])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4408,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_10])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1606,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1928,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),X1) ),
    inference(resolution,[status(thm)],[c_1606,c_11])).

cnf(c_3215,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1928,c_6])).

cnf(c_4824,plain,
    ( r2_hidden(sK2(k1_xboole_0,X0),X0)
    | k1_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_4408,c_3215])).

cnf(c_5659,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4824,c_1606])).

cnf(c_7835,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5659,c_6])).

cnf(c_516,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_515,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1914,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_516,c_515])).

cnf(c_7838,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7835,c_1914])).

cnf(c_8409,plain,
    ( X0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_7838,c_516])).

cnf(c_5631,plain,
    ( r2_hidden(sK2(k1_xboole_0,X0),X0)
    | X0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4824,c_1914])).

cnf(c_10632,plain,
    ( r2_hidden(sK2(k1_xboole_0,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_8409,c_5631])).

cnf(c_1280,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK6,X1))
    | r2_hidden(X1,k1_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_375,c_10])).

cnf(c_11209,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | k1_xboole_0 = k11_relat_1(sK6,X0) ),
    inference(resolution,[status(thm)],[c_10632,c_1280])).

cnf(c_13427,plain,
    ( k1_xboole_0 = k11_relat_1(sK6,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11209,c_14])).

cnf(c_13749,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13427,c_1914])).

cnf(c_29956,plain,
    ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29810,c_13749])).

cnf(c_934,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_235,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_236,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_376,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK6)
    | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
    inference(prop_impl,[status(thm)],[c_236])).

cnf(c_377,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_931,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1958,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_931])).

cnf(c_29998,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29956,c_1958])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,k1_relat_1(sK6))
    | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,plain,
    ( k1_xboole_0 != k11_relat_1(sK6,sK5)
    | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_31004,plain,
    ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29998,c_18,c_13427])).

cnf(c_942,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_944,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2183,plain,
    ( r2_hidden(sK0(X0,X1),X2) != iProver_top
    | r1_xboole_0(X2,X0) != iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_943,c_945])).

cnf(c_5944,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_2183])).

cnf(c_5981,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_5944])).

cnf(c_6146,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5981,c_2185])).

cnf(c_31009,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_31004,c_6146])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.80/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.49  
% 7.80/1.49  ------  iProver source info
% 7.80/1.49  
% 7.80/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.49  git: non_committed_changes: false
% 7.80/1.49  git: last_make_outside_of_git: false
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  ------ Parsing...
% 7.80/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  ------ Proving...
% 7.80/1.49  ------ Problem Properties 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  clauses                                 16
% 7.80/1.49  conjectures                             2
% 7.80/1.49  EPR                                     2
% 7.80/1.49  Horn                                    12
% 7.80/1.49  unary                                   2
% 7.80/1.49  binary                                  9
% 7.80/1.49  lits                                    35
% 7.80/1.49  lits eq                                 9
% 7.80/1.49  fd_pure                                 0
% 7.80/1.49  fd_pseudo                               0
% 7.80/1.49  fd_cond                                 0
% 7.80/1.49  fd_pseudo_cond                          4
% 7.80/1.49  AC symbols                              0
% 7.80/1.49  
% 7.80/1.49  ------ Input Options Time Limit: Unbounded
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  Current options:
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS status Theorem for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49   Resolution empty clause
% 7.80/1.49  
% 7.80/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  fof(f3,axiom,(
% 7.80/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f15,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.80/1.49    inference(nnf_transformation,[],[f3])).
% 7.80/1.49  
% 7.80/1.49  fof(f16,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.80/1.49    inference(rectify,[],[f15])).
% 7.80/1.49  
% 7.80/1.49  fof(f17,plain,(
% 7.80/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f18,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 7.80/1.49  
% 7.80/1.49  fof(f36,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f18])).
% 7.80/1.49  
% 7.80/1.49  fof(f4,axiom,(
% 7.80/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f38,plain,(
% 7.80/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f4])).
% 7.80/1.49  
% 7.80/1.49  fof(f49,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 7.80/1.49    inference(definition_unfolding,[],[f36,f38])).
% 7.80/1.49  
% 7.80/1.49  fof(f1,axiom,(
% 7.80/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f9,plain,(
% 7.80/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(rectify,[],[f1])).
% 7.80/1.49  
% 7.80/1.49  fof(f10,plain,(
% 7.80/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(ennf_transformation,[],[f9])).
% 7.80/1.49  
% 7.80/1.49  fof(f13,plain,(
% 7.80/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f14,plain,(
% 7.80/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 7.80/1.49  
% 7.80/1.49  fof(f30,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f14])).
% 7.80/1.49  
% 7.80/1.49  fof(f6,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f11,plain,(
% 7.80/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 7.80/1.49    inference(ennf_transformation,[],[f6])).
% 7.80/1.49  
% 7.80/1.49  fof(f25,plain,(
% 7.80/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 7.80/1.49    inference(nnf_transformation,[],[f11])).
% 7.80/1.49  
% 7.80/1.49  fof(f44,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f25])).
% 7.80/1.49  
% 7.80/1.49  fof(f7,conjecture,(
% 7.80/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f8,negated_conjecture,(
% 7.80/1.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.80/1.49    inference(negated_conjecture,[],[f7])).
% 7.80/1.49  
% 7.80/1.49  fof(f12,plain,(
% 7.80/1.49    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 7.80/1.49    inference(ennf_transformation,[],[f8])).
% 7.80/1.49  
% 7.80/1.49  fof(f26,plain,(
% 7.80/1.49    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 7.80/1.49    inference(nnf_transformation,[],[f12])).
% 7.80/1.49  
% 7.80/1.49  fof(f27,plain,(
% 7.80/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 7.80/1.49    inference(flattening,[],[f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f28,plain,(
% 7.80/1.49    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f29,plain,(
% 7.80/1.49    (k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))) & (k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))) & v1_relat_1(sK6)),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f28])).
% 7.80/1.49  
% 7.80/1.49  fof(f45,plain,(
% 7.80/1.49    v1_relat_1(sK6)),
% 7.80/1.49    inference(cnf_transformation,[],[f29])).
% 7.80/1.49  
% 7.80/1.49  fof(f5,axiom,(
% 7.80/1.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f19,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.80/1.49    inference(nnf_transformation,[],[f5])).
% 7.80/1.49  
% 7.80/1.49  fof(f20,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.80/1.49    inference(rectify,[],[f19])).
% 7.80/1.49  
% 7.80/1.49  fof(f23,plain,(
% 7.80/1.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f22,plain,(
% 7.80/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f21,plain,(
% 7.80/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f24,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).
% 7.80/1.49  
% 7.80/1.49  fof(f40,plain,(
% 7.80/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.80/1.49    inference(cnf_transformation,[],[f24])).
% 7.80/1.49  
% 7.80/1.49  fof(f55,plain,(
% 7.80/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.80/1.49    inference(equality_resolution,[],[f40])).
% 7.80/1.49  
% 7.80/1.49  fof(f35,plain,(
% 7.80/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.80/1.49    inference(cnf_transformation,[],[f18])).
% 7.80/1.49  
% 7.80/1.49  fof(f50,plain,(
% 7.80/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 7.80/1.49    inference(definition_unfolding,[],[f35,f38])).
% 7.80/1.49  
% 7.80/1.49  fof(f52,plain,(
% 7.80/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 7.80/1.49    inference(equality_resolution,[],[f50])).
% 7.80/1.49  
% 7.80/1.49  fof(f53,plain,(
% 7.80/1.49    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 7.80/1.49    inference(equality_resolution,[],[f52])).
% 7.80/1.49  
% 7.80/1.49  fof(f32,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f14])).
% 7.80/1.49  
% 7.80/1.49  fof(f47,plain,(
% 7.80/1.49    k1_xboole_0 = k11_relat_1(sK6,sK5) | ~r2_hidden(sK5,k1_relat_1(sK6))),
% 7.80/1.49    inference(cnf_transformation,[],[f29])).
% 7.80/1.49  
% 7.80/1.49  fof(f41,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f24])).
% 7.80/1.49  
% 7.80/1.49  fof(f2,axiom,(
% 7.80/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f33,plain,(
% 7.80/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f2])).
% 7.80/1.49  
% 7.80/1.49  fof(f39,plain,(
% 7.80/1.49    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.80/1.49    inference(cnf_transformation,[],[f24])).
% 7.80/1.49  
% 7.80/1.49  fof(f56,plain,(
% 7.80/1.49    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.80/1.49    inference(equality_resolution,[],[f39])).
% 7.80/1.49  
% 7.80/1.49  fof(f43,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f25])).
% 7.80/1.49  
% 7.80/1.49  fof(f46,plain,(
% 7.80/1.49    k1_xboole_0 != k11_relat_1(sK6,sK5) | r2_hidden(sK5,k1_relat_1(sK6))),
% 7.80/1.49    inference(cnf_transformation,[],[f29])).
% 7.80/1.49  
% 7.80/1.49  fof(f31,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f14])).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5,plain,
% 7.80/1.49      ( r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0 | k2_tarski(X0,X0) = X1 ),
% 7.80/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_940,plain,
% 7.80/1.49      ( sK1(X0,X1) = X0
% 7.80/1.49      | k2_tarski(X0,X0) = X1
% 7.80/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2,plain,
% 7.80/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_943,plain,
% 7.80/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.80/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 7.80/1.49      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.80/1.49      | ~ v1_relat_1(X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_16,negated_conjecture,
% 7.80/1.49      ( v1_relat_1(sK6) ),
% 7.80/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_247,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 7.80/1.49      | r2_hidden(k4_tarski(X2,X0),X1)
% 7.80/1.49      | sK6 != X1 ),
% 7.80/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_248,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 7.80/1.49      inference(unflattening,[status(thm)],[c_247]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_374,plain,
% 7.80/1.49      ( r2_hidden(k4_tarski(X1,X0),sK6) | ~ r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 7.80/1.49      inference(prop_impl,[status(thm)],[c_248]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_375,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(k4_tarski(X1,X0),sK6) ),
% 7.80/1.49      inference(renaming,[status(thm)],[c_374]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_930,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 7.80/1.49      | r2_hidden(k4_tarski(X1,X0),sK6) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1564,plain,
% 7.80/1.49      ( r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK6,X0),X1)),sK6) = iProver_top
% 7.80/1.49      | r1_xboole_0(k11_relat_1(sK6,X0),X1) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_943,c_930]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_935,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.80/1.49      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3923,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 7.80/1.49      | r1_xboole_0(k11_relat_1(sK6,X0),X1) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1564,c_935]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6,plain,
% 7.80/1.49      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 7.80/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_939,plain,
% 7.80/1.49      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_0,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_945,plain,
% 7.80/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.80/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.80/1.49      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2185,plain,
% 7.80/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.80/1.49      | r1_xboole_0(X1,k2_tarski(X0,X0)) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_939,c_945]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4317,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 7.80/1.49      | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3923,c_2185]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5020,plain,
% 7.80/1.49      ( sK1(X0,k11_relat_1(sK6,X1)) = X0
% 7.80/1.49      | k2_tarski(X0,X0) = k11_relat_1(sK6,X1)
% 7.80/1.49      | r2_hidden(X1,k1_relat_1(sK6)) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_940,c_4317]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_14,negated_conjecture,
% 7.80/1.49      ( ~ r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 7.80/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_933,plain,
% 7.80/1.49      ( k1_xboole_0 = k11_relat_1(sK6,sK5)
% 7.80/1.49      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_29810,plain,
% 7.80/1.49      ( k11_relat_1(sK6,sK5) = k1_xboole_0
% 7.80/1.49      | sK1(X0,k11_relat_1(sK6,sK5)) = X0
% 7.80/1.49      | k2_tarski(X0,X0) = k11_relat_1(sK6,sK5) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_5020,c_933]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9,plain,
% 7.80/1.49      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 7.80/1.49      | r2_hidden(sK2(X0,X1),X1)
% 7.80/1.49      | k1_relat_1(X0) = X1 ),
% 7.80/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4408,plain,
% 7.80/1.49      ( r2_hidden(sK2(X0,X1),X1)
% 7.80/1.49      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 7.80/1.49      | k1_relat_1(X0) = X1 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_9,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3,plain,
% 7.80/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.80/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1606,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_0,c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.80/1.49      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1928,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 7.80/1.49      | ~ r2_hidden(k4_tarski(X0,sK4(k1_xboole_0,X0)),X1) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_1606,c_11]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3215,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_1928,c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4824,plain,
% 7.80/1.49      ( r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_relat_1(k1_xboole_0) = X0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_4408,c_3215]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5659,plain,
% 7.80/1.49      ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0)
% 7.80/1.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_4824,c_1606]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7835,plain,
% 7.80/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_5659,c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_516,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_515,plain,( X0 = X0 ),theory(equality) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1914,plain,
% 7.80/1.49      ( X0 != X1 | X1 = X0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_516,c_515]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7838,plain,
% 7.80/1.49      ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_7835,c_1914]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_8409,plain,
% 7.80/1.49      ( X0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_7838,c_516]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5631,plain,
% 7.80/1.49      ( r2_hidden(sK2(k1_xboole_0,X0),X0) | X0 = k1_relat_1(k1_xboole_0) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_4824,c_1914]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10632,plain,
% 7.80/1.49      ( r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_8409,c_5631]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1280,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k11_relat_1(sK6,X1)) | r2_hidden(X1,k1_relat_1(sK6)) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_375,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11209,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(sK6)) | k1_xboole_0 = k11_relat_1(sK6,X0) ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_10632,c_1280]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13427,plain,
% 7.80/1.49      ( k1_xboole_0 = k11_relat_1(sK6,sK5) ),
% 7.80/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_11209,c_14]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13749,plain,
% 7.80/1.49      ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
% 7.80/1.49      inference(resolution,[status(thm)],[c_13427,c_1914]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_29956,plain,
% 7.80/1.49      ( k11_relat_1(sK6,sK5) = k1_xboole_0 ),
% 7.80/1.49      inference(global_propositional_subsumption,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_29810,c_13749]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_934,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.80/1.49      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.80/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.80/1.49      | ~ v1_relat_1(X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_235,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 7.80/1.49      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.80/1.49      | sK6 != X1 ),
% 7.80/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_236,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 7.80/1.49      inference(unflattening,[status(thm)],[c_235]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_376,plain,
% 7.80/1.49      ( ~ r2_hidden(k4_tarski(X1,X0),sK6) | r2_hidden(X0,k11_relat_1(sK6,X1)) ),
% 7.80/1.49      inference(prop_impl,[status(thm)],[c_236]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_377,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(sK6,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK6) ),
% 7.80/1.49      inference(renaming,[status(thm)],[c_376]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_931,plain,
% 7.80/1.49      ( r2_hidden(X0,k11_relat_1(sK6,X1)) = iProver_top
% 7.80/1.49      | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1958,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.80/1.49      | r2_hidden(sK4(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_934,c_931]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_29998,plain,
% 7.80/1.49      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top
% 7.80/1.49      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_29956,c_1958]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_15,negated_conjecture,
% 7.80/1.49      ( r2_hidden(sK5,k1_relat_1(sK6)) | k1_xboole_0 != k11_relat_1(sK6,sK5) ),
% 7.80/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_18,plain,
% 7.80/1.49      ( k1_xboole_0 != k11_relat_1(sK6,sK5)
% 7.80/1.49      | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_31004,plain,
% 7.80/1.49      ( r2_hidden(sK4(sK6,sK5),k1_xboole_0) = iProver_top ),
% 7.80/1.49      inference(global_propositional_subsumption,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_29998,c_18,c_13427]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_942,plain,
% 7.80/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1,plain,
% 7.80/1.49      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_944,plain,
% 7.80/1.49      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.80/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2183,plain,
% 7.80/1.49      ( r2_hidden(sK0(X0,X1),X2) != iProver_top
% 7.80/1.49      | r1_xboole_0(X2,X0) != iProver_top
% 7.80/1.49      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_943,c_945]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5944,plain,
% 7.80/1.49      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_944,c_2183]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5981,plain,
% 7.80/1.49      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_942,c_5944]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6146,plain,
% 7.80/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_5981,c_2185]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_31009,plain,
% 7.80/1.49      ( $false ),
% 7.80/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_31004,c_6146]) ).
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  ------                               Statistics
% 7.80/1.49  
% 7.80/1.49  ------ Selected
% 7.80/1.49  
% 7.80/1.49  total_time:                             0.774
% 7.80/1.49  
%------------------------------------------------------------------------------
