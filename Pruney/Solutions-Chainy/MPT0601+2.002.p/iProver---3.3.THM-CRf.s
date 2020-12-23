%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:18 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 258 expanded)
%              Number of clauses        :   54 (  91 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  263 ( 855 expanded)
%              Number of equality atoms :   99 ( 273 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
        | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
      & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
        | r2_hidden(sK4,k1_relat_1(sK5)) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
      | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
    & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
      | r2_hidden(sK4,k1_relat_1(sK5)) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f42,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

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
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f44,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,
    ( k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_703,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_212,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_279,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_212])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_279])).

cnf(c_695,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1150,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK5,X0))),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_695])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_700,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4036,plain,
    ( k11_relat_1(sK5,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_700])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_698,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4066,plain,
    ( k11_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4036,c_698])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_699,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_199,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_200,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_281,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_200])).

cnf(c_282,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_696,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_1132,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK3(sK5,X0),k11_relat_1(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_696])).

cnf(c_4188,plain,
    ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4066,c_1132])).

cnf(c_18,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_862,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_863,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) = iProver_top
    | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_884,plain,
    ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_885,plain,
    ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1046,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X1 != k11_relat_1(sK5,sK4)
    | X0 != sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_2391,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X0 != sK3(sK5,sK4)
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2800,plain,
    ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
    | sK3(sK5,sK4) != sK3(sK5,sK4)
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_2802,plain,
    ( sK3(sK5,sK4) != sK3(sK5,sK4)
    | k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4)) != iProver_top
    | r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2800])).

cnf(c_364,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2801,plain,
    ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_697,plain,
    ( k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4177,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4066,c_697])).

cnf(c_4178,plain,
    ( r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4177])).

cnf(c_4499,plain,
    ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4188,c_18,c_863,c_885,c_2802,c_2801,c_4178])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_705,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2683,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_705])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_707,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1504,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_707])).

cnf(c_2835,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2683,c_1504])).

cnf(c_2842,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_703,c_2835])).

cnf(c_2867,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2842,c_2835])).

cnf(c_4504,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4499,c_2867])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:38:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.08/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.97  
% 2.08/0.97  ------  iProver source info
% 2.08/0.97  
% 2.08/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.97  git: non_committed_changes: false
% 2.08/0.97  git: last_make_outside_of_git: false
% 2.08/0.97  
% 2.08/0.97  ------ 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options
% 2.08/0.97  
% 2.08/0.97  --out_options                           all
% 2.08/0.97  --tptp_safe_out                         true
% 2.08/0.97  --problem_path                          ""
% 2.08/0.97  --include_path                          ""
% 2.08/0.97  --clausifier                            res/vclausify_rel
% 2.08/0.97  --clausifier_options                    --mode clausify
% 2.08/0.97  --stdin                                 false
% 2.08/0.97  --stats_out                             all
% 2.08/0.97  
% 2.08/0.97  ------ General Options
% 2.08/0.97  
% 2.08/0.97  --fof                                   false
% 2.08/0.97  --time_out_real                         305.
% 2.08/0.97  --time_out_virtual                      -1.
% 2.08/0.97  --symbol_type_check                     false
% 2.08/0.97  --clausify_out                          false
% 2.08/0.97  --sig_cnt_out                           false
% 2.08/0.97  --trig_cnt_out                          false
% 2.08/0.97  --trig_cnt_out_tolerance                1.
% 2.08/0.97  --trig_cnt_out_sk_spl                   false
% 2.08/0.97  --abstr_cl_out                          false
% 2.08/0.97  
% 2.08/0.97  ------ Global Options
% 2.08/0.97  
% 2.08/0.97  --schedule                              default
% 2.08/0.97  --add_important_lit                     false
% 2.08/0.97  --prop_solver_per_cl                    1000
% 2.08/0.97  --min_unsat_core                        false
% 2.08/0.97  --soft_assumptions                      false
% 2.08/0.97  --soft_lemma_size                       3
% 2.08/0.97  --prop_impl_unit_size                   0
% 2.08/0.97  --prop_impl_unit                        []
% 2.08/0.97  --share_sel_clauses                     true
% 2.08/0.97  --reset_solvers                         false
% 2.08/0.97  --bc_imp_inh                            [conj_cone]
% 2.08/0.97  --conj_cone_tolerance                   3.
% 2.08/0.97  --extra_neg_conj                        none
% 2.08/0.97  --large_theory_mode                     true
% 2.08/0.97  --prolific_symb_bound                   200
% 2.08/0.97  --lt_threshold                          2000
% 2.08/0.97  --clause_weak_htbl                      true
% 2.08/0.97  --gc_record_bc_elim                     false
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing Options
% 2.08/0.97  
% 2.08/0.97  --preprocessing_flag                    true
% 2.08/0.97  --time_out_prep_mult                    0.1
% 2.08/0.97  --splitting_mode                        input
% 2.08/0.97  --splitting_grd                         true
% 2.08/0.97  --splitting_cvd                         false
% 2.08/0.97  --splitting_cvd_svl                     false
% 2.08/0.97  --splitting_nvd                         32
% 2.08/0.97  --sub_typing                            true
% 2.08/0.97  --prep_gs_sim                           true
% 2.08/0.97  --prep_unflatten                        true
% 2.08/0.97  --prep_res_sim                          true
% 2.08/0.97  --prep_upred                            true
% 2.08/0.97  --prep_sem_filter                       exhaustive
% 2.08/0.97  --prep_sem_filter_out                   false
% 2.08/0.97  --pred_elim                             true
% 2.08/0.97  --res_sim_input                         true
% 2.08/0.97  --eq_ax_congr_red                       true
% 2.08/0.97  --pure_diseq_elim                       true
% 2.08/0.97  --brand_transform                       false
% 2.08/0.97  --non_eq_to_eq                          false
% 2.08/0.97  --prep_def_merge                        true
% 2.08/0.97  --prep_def_merge_prop_impl              false
% 2.08/0.97  --prep_def_merge_mbd                    true
% 2.08/0.97  --prep_def_merge_tr_red                 false
% 2.08/0.97  --prep_def_merge_tr_cl                  false
% 2.08/0.97  --smt_preprocessing                     true
% 2.08/0.97  --smt_ac_axioms                         fast
% 2.08/0.97  --preprocessed_out                      false
% 2.08/0.97  --preprocessed_stats                    false
% 2.08/0.97  
% 2.08/0.97  ------ Abstraction refinement Options
% 2.08/0.97  
% 2.08/0.97  --abstr_ref                             []
% 2.08/0.97  --abstr_ref_prep                        false
% 2.08/0.97  --abstr_ref_until_sat                   false
% 2.08/0.97  --abstr_ref_sig_restrict                funpre
% 2.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.97  --abstr_ref_under                       []
% 2.08/0.97  
% 2.08/0.97  ------ SAT Options
% 2.08/0.97  
% 2.08/0.97  --sat_mode                              false
% 2.08/0.97  --sat_fm_restart_options                ""
% 2.08/0.97  --sat_gr_def                            false
% 2.08/0.97  --sat_epr_types                         true
% 2.08/0.97  --sat_non_cyclic_types                  false
% 2.08/0.97  --sat_finite_models                     false
% 2.08/0.97  --sat_fm_lemmas                         false
% 2.08/0.97  --sat_fm_prep                           false
% 2.08/0.97  --sat_fm_uc_incr                        true
% 2.08/0.97  --sat_out_model                         small
% 2.08/0.97  --sat_out_clauses                       false
% 2.08/0.97  
% 2.08/0.97  ------ QBF Options
% 2.08/0.97  
% 2.08/0.97  --qbf_mode                              false
% 2.08/0.97  --qbf_elim_univ                         false
% 2.08/0.97  --qbf_dom_inst                          none
% 2.08/0.97  --qbf_dom_pre_inst                      false
% 2.08/0.97  --qbf_sk_in                             false
% 2.08/0.97  --qbf_pred_elim                         true
% 2.08/0.97  --qbf_split                             512
% 2.08/0.97  
% 2.08/0.97  ------ BMC1 Options
% 2.08/0.97  
% 2.08/0.97  --bmc1_incremental                      false
% 2.08/0.97  --bmc1_axioms                           reachable_all
% 2.08/0.97  --bmc1_min_bound                        0
% 2.08/0.97  --bmc1_max_bound                        -1
% 2.08/0.97  --bmc1_max_bound_default                -1
% 2.08/0.97  --bmc1_symbol_reachability              true
% 2.08/0.97  --bmc1_property_lemmas                  false
% 2.08/0.97  --bmc1_k_induction                      false
% 2.08/0.97  --bmc1_non_equiv_states                 false
% 2.08/0.97  --bmc1_deadlock                         false
% 2.08/0.97  --bmc1_ucm                              false
% 2.08/0.97  --bmc1_add_unsat_core                   none
% 2.08/0.97  --bmc1_unsat_core_children              false
% 2.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.97  --bmc1_out_stat                         full
% 2.08/0.97  --bmc1_ground_init                      false
% 2.08/0.97  --bmc1_pre_inst_next_state              false
% 2.08/0.97  --bmc1_pre_inst_state                   false
% 2.08/0.97  --bmc1_pre_inst_reach_state             false
% 2.08/0.97  --bmc1_out_unsat_core                   false
% 2.08/0.97  --bmc1_aig_witness_out                  false
% 2.08/0.97  --bmc1_verbose                          false
% 2.08/0.97  --bmc1_dump_clauses_tptp                false
% 2.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.97  --bmc1_dump_file                        -
% 2.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.97  --bmc1_ucm_extend_mode                  1
% 2.08/0.97  --bmc1_ucm_init_mode                    2
% 2.08/0.97  --bmc1_ucm_cone_mode                    none
% 2.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.97  --bmc1_ucm_relax_model                  4
% 2.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.97  --bmc1_ucm_layered_model                none
% 2.08/0.97  --bmc1_ucm_max_lemma_size               10
% 2.08/0.97  
% 2.08/0.97  ------ AIG Options
% 2.08/0.97  
% 2.08/0.97  --aig_mode                              false
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation Options
% 2.08/0.97  
% 2.08/0.97  --instantiation_flag                    true
% 2.08/0.97  --inst_sos_flag                         false
% 2.08/0.97  --inst_sos_phase                        true
% 2.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel_side                     num_symb
% 2.08/0.97  --inst_solver_per_active                1400
% 2.08/0.97  --inst_solver_calls_frac                1.
% 2.08/0.97  --inst_passive_queue_type               priority_queues
% 2.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.97  --inst_passive_queues_freq              [25;2]
% 2.08/0.97  --inst_dismatching                      true
% 2.08/0.97  --inst_eager_unprocessed_to_passive     true
% 2.08/0.97  --inst_prop_sim_given                   true
% 2.08/0.97  --inst_prop_sim_new                     false
% 2.08/0.97  --inst_subs_new                         false
% 2.08/0.97  --inst_eq_res_simp                      false
% 2.08/0.97  --inst_subs_given                       false
% 2.08/0.97  --inst_orphan_elimination               true
% 2.08/0.97  --inst_learning_loop_flag               true
% 2.08/0.97  --inst_learning_start                   3000
% 2.08/0.97  --inst_learning_factor                  2
% 2.08/0.97  --inst_start_prop_sim_after_learn       3
% 2.08/0.97  --inst_sel_renew                        solver
% 2.08/0.97  --inst_lit_activity_flag                true
% 2.08/0.97  --inst_restr_to_given                   false
% 2.08/0.97  --inst_activity_threshold               500
% 2.08/0.97  --inst_out_proof                        true
% 2.08/0.97  
% 2.08/0.97  ------ Resolution Options
% 2.08/0.97  
% 2.08/0.97  --resolution_flag                       true
% 2.08/0.97  --res_lit_sel                           adaptive
% 2.08/0.97  --res_lit_sel_side                      none
% 2.08/0.97  --res_ordering                          kbo
% 2.08/0.97  --res_to_prop_solver                    active
% 2.08/0.97  --res_prop_simpl_new                    false
% 2.08/0.97  --res_prop_simpl_given                  true
% 2.08/0.97  --res_passive_queue_type                priority_queues
% 2.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.97  --res_passive_queues_freq               [15;5]
% 2.08/0.97  --res_forward_subs                      full
% 2.08/0.97  --res_backward_subs                     full
% 2.08/0.97  --res_forward_subs_resolution           true
% 2.08/0.97  --res_backward_subs_resolution          true
% 2.08/0.97  --res_orphan_elimination                true
% 2.08/0.97  --res_time_limit                        2.
% 2.08/0.97  --res_out_proof                         true
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Options
% 2.08/0.97  
% 2.08/0.97  --superposition_flag                    true
% 2.08/0.97  --sup_passive_queue_type                priority_queues
% 2.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.97  --demod_completeness_check              fast
% 2.08/0.97  --demod_use_ground                      true
% 2.08/0.97  --sup_to_prop_solver                    passive
% 2.08/0.97  --sup_prop_simpl_new                    true
% 2.08/0.97  --sup_prop_simpl_given                  true
% 2.08/0.97  --sup_fun_splitting                     false
% 2.08/0.97  --sup_smt_interval                      50000
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Simplification Setup
% 2.08/0.97  
% 2.08/0.97  --sup_indices_passive                   []
% 2.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_full_bw                           [BwDemod]
% 2.08/0.97  --sup_immed_triv                        [TrivRules]
% 2.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_immed_bw_main                     []
% 2.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  
% 2.08/0.97  ------ Combination Options
% 2.08/0.97  
% 2.08/0.97  --comb_res_mult                         3
% 2.08/0.97  --comb_sup_mult                         2
% 2.08/0.97  --comb_inst_mult                        10
% 2.08/0.97  
% 2.08/0.97  ------ Debug Options
% 2.08/0.97  
% 2.08/0.97  --dbg_backtrace                         false
% 2.08/0.97  --dbg_dump_prop_clauses                 false
% 2.08/0.97  --dbg_dump_prop_clauses_file            -
% 2.08/0.97  --dbg_out_stat                          false
% 2.08/0.97  ------ Parsing...
% 2.08/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.97  ------ Proving...
% 2.08/0.97  ------ Problem Properties 
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  clauses                                 15
% 2.08/0.97  conjectures                             2
% 2.08/0.97  EPR                                     0
% 2.08/0.97  Horn                                    10
% 2.08/0.97  unary                                   2
% 2.08/0.97  binary                                  7
% 2.08/0.97  lits                                    34
% 2.08/0.97  lits eq                                 7
% 2.08/0.97  fd_pure                                 0
% 2.08/0.97  fd_pseudo                               0
% 2.08/0.97  fd_cond                                 1
% 2.08/0.97  fd_pseudo_cond                          2
% 2.08/0.97  AC symbols                              0
% 2.08/0.97  
% 2.08/0.97  ------ Schedule dynamic 5 is on 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  ------ 
% 2.08/0.97  Current options:
% 2.08/0.97  ------ 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options
% 2.08/0.97  
% 2.08/0.97  --out_options                           all
% 2.08/0.97  --tptp_safe_out                         true
% 2.08/0.97  --problem_path                          ""
% 2.08/0.97  --include_path                          ""
% 2.08/0.97  --clausifier                            res/vclausify_rel
% 2.08/0.97  --clausifier_options                    --mode clausify
% 2.08/0.97  --stdin                                 false
% 2.08/0.97  --stats_out                             all
% 2.08/0.97  
% 2.08/0.97  ------ General Options
% 2.08/0.97  
% 2.08/0.97  --fof                                   false
% 2.08/0.97  --time_out_real                         305.
% 2.08/0.97  --time_out_virtual                      -1.
% 2.08/0.97  --symbol_type_check                     false
% 2.08/0.97  --clausify_out                          false
% 2.08/0.97  --sig_cnt_out                           false
% 2.08/0.97  --trig_cnt_out                          false
% 2.08/0.97  --trig_cnt_out_tolerance                1.
% 2.08/0.97  --trig_cnt_out_sk_spl                   false
% 2.08/0.97  --abstr_cl_out                          false
% 2.08/0.97  
% 2.08/0.97  ------ Global Options
% 2.08/0.97  
% 2.08/0.97  --schedule                              default
% 2.08/0.97  --add_important_lit                     false
% 2.08/0.97  --prop_solver_per_cl                    1000
% 2.08/0.97  --min_unsat_core                        false
% 2.08/0.97  --soft_assumptions                      false
% 2.08/0.97  --soft_lemma_size                       3
% 2.08/0.97  --prop_impl_unit_size                   0
% 2.08/0.97  --prop_impl_unit                        []
% 2.08/0.97  --share_sel_clauses                     true
% 2.08/0.97  --reset_solvers                         false
% 2.08/0.97  --bc_imp_inh                            [conj_cone]
% 2.08/0.97  --conj_cone_tolerance                   3.
% 2.08/0.97  --extra_neg_conj                        none
% 2.08/0.97  --large_theory_mode                     true
% 2.08/0.97  --prolific_symb_bound                   200
% 2.08/0.97  --lt_threshold                          2000
% 2.08/0.97  --clause_weak_htbl                      true
% 2.08/0.97  --gc_record_bc_elim                     false
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing Options
% 2.08/0.97  
% 2.08/0.97  --preprocessing_flag                    true
% 2.08/0.97  --time_out_prep_mult                    0.1
% 2.08/0.97  --splitting_mode                        input
% 2.08/0.97  --splitting_grd                         true
% 2.08/0.97  --splitting_cvd                         false
% 2.08/0.97  --splitting_cvd_svl                     false
% 2.08/0.97  --splitting_nvd                         32
% 2.08/0.97  --sub_typing                            true
% 2.08/0.97  --prep_gs_sim                           true
% 2.08/0.97  --prep_unflatten                        true
% 2.08/0.97  --prep_res_sim                          true
% 2.08/0.97  --prep_upred                            true
% 2.08/0.97  --prep_sem_filter                       exhaustive
% 2.08/0.97  --prep_sem_filter_out                   false
% 2.08/0.97  --pred_elim                             true
% 2.08/0.97  --res_sim_input                         true
% 2.08/0.97  --eq_ax_congr_red                       true
% 2.08/0.97  --pure_diseq_elim                       true
% 2.08/0.97  --brand_transform                       false
% 2.08/0.97  --non_eq_to_eq                          false
% 2.08/0.97  --prep_def_merge                        true
% 2.08/0.97  --prep_def_merge_prop_impl              false
% 2.08/0.97  --prep_def_merge_mbd                    true
% 2.08/0.97  --prep_def_merge_tr_red                 false
% 2.08/0.97  --prep_def_merge_tr_cl                  false
% 2.08/0.97  --smt_preprocessing                     true
% 2.08/0.97  --smt_ac_axioms                         fast
% 2.08/0.97  --preprocessed_out                      false
% 2.08/0.97  --preprocessed_stats                    false
% 2.08/0.97  
% 2.08/0.97  ------ Abstraction refinement Options
% 2.08/0.97  
% 2.08/0.97  --abstr_ref                             []
% 2.08/0.97  --abstr_ref_prep                        false
% 2.08/0.97  --abstr_ref_until_sat                   false
% 2.08/0.97  --abstr_ref_sig_restrict                funpre
% 2.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.97  --abstr_ref_under                       []
% 2.08/0.97  
% 2.08/0.97  ------ SAT Options
% 2.08/0.97  
% 2.08/0.97  --sat_mode                              false
% 2.08/0.97  --sat_fm_restart_options                ""
% 2.08/0.97  --sat_gr_def                            false
% 2.08/0.97  --sat_epr_types                         true
% 2.08/0.97  --sat_non_cyclic_types                  false
% 2.08/0.97  --sat_finite_models                     false
% 2.08/0.97  --sat_fm_lemmas                         false
% 2.08/0.97  --sat_fm_prep                           false
% 2.08/0.97  --sat_fm_uc_incr                        true
% 2.08/0.97  --sat_out_model                         small
% 2.08/0.97  --sat_out_clauses                       false
% 2.08/0.97  
% 2.08/0.97  ------ QBF Options
% 2.08/0.97  
% 2.08/0.97  --qbf_mode                              false
% 2.08/0.97  --qbf_elim_univ                         false
% 2.08/0.97  --qbf_dom_inst                          none
% 2.08/0.97  --qbf_dom_pre_inst                      false
% 2.08/0.97  --qbf_sk_in                             false
% 2.08/0.97  --qbf_pred_elim                         true
% 2.08/0.97  --qbf_split                             512
% 2.08/0.97  
% 2.08/0.97  ------ BMC1 Options
% 2.08/0.97  
% 2.08/0.97  --bmc1_incremental                      false
% 2.08/0.97  --bmc1_axioms                           reachable_all
% 2.08/0.97  --bmc1_min_bound                        0
% 2.08/0.97  --bmc1_max_bound                        -1
% 2.08/0.97  --bmc1_max_bound_default                -1
% 2.08/0.97  --bmc1_symbol_reachability              true
% 2.08/0.97  --bmc1_property_lemmas                  false
% 2.08/0.97  --bmc1_k_induction                      false
% 2.08/0.97  --bmc1_non_equiv_states                 false
% 2.08/0.97  --bmc1_deadlock                         false
% 2.08/0.97  --bmc1_ucm                              false
% 2.08/0.97  --bmc1_add_unsat_core                   none
% 2.08/0.97  --bmc1_unsat_core_children              false
% 2.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.97  --bmc1_out_stat                         full
% 2.08/0.97  --bmc1_ground_init                      false
% 2.08/0.97  --bmc1_pre_inst_next_state              false
% 2.08/0.97  --bmc1_pre_inst_state                   false
% 2.08/0.97  --bmc1_pre_inst_reach_state             false
% 2.08/0.97  --bmc1_out_unsat_core                   false
% 2.08/0.97  --bmc1_aig_witness_out                  false
% 2.08/0.97  --bmc1_verbose                          false
% 2.08/0.97  --bmc1_dump_clauses_tptp                false
% 2.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.97  --bmc1_dump_file                        -
% 2.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.97  --bmc1_ucm_extend_mode                  1
% 2.08/0.97  --bmc1_ucm_init_mode                    2
% 2.08/0.97  --bmc1_ucm_cone_mode                    none
% 2.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.97  --bmc1_ucm_relax_model                  4
% 2.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.97  --bmc1_ucm_layered_model                none
% 2.08/0.97  --bmc1_ucm_max_lemma_size               10
% 2.08/0.97  
% 2.08/0.97  ------ AIG Options
% 2.08/0.97  
% 2.08/0.97  --aig_mode                              false
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation Options
% 2.08/0.97  
% 2.08/0.97  --instantiation_flag                    true
% 2.08/0.97  --inst_sos_flag                         false
% 2.08/0.97  --inst_sos_phase                        true
% 2.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel_side                     none
% 2.08/0.97  --inst_solver_per_active                1400
% 2.08/0.97  --inst_solver_calls_frac                1.
% 2.08/0.97  --inst_passive_queue_type               priority_queues
% 2.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.97  --inst_passive_queues_freq              [25;2]
% 2.08/0.97  --inst_dismatching                      true
% 2.08/0.97  --inst_eager_unprocessed_to_passive     true
% 2.08/0.97  --inst_prop_sim_given                   true
% 2.08/0.97  --inst_prop_sim_new                     false
% 2.08/0.97  --inst_subs_new                         false
% 2.08/0.97  --inst_eq_res_simp                      false
% 2.08/0.97  --inst_subs_given                       false
% 2.08/0.97  --inst_orphan_elimination               true
% 2.08/0.97  --inst_learning_loop_flag               true
% 2.08/0.97  --inst_learning_start                   3000
% 2.08/0.97  --inst_learning_factor                  2
% 2.08/0.97  --inst_start_prop_sim_after_learn       3
% 2.08/0.97  --inst_sel_renew                        solver
% 2.08/0.97  --inst_lit_activity_flag                true
% 2.08/0.97  --inst_restr_to_given                   false
% 2.08/0.97  --inst_activity_threshold               500
% 2.08/0.97  --inst_out_proof                        true
% 2.08/0.97  
% 2.08/0.97  ------ Resolution Options
% 2.08/0.97  
% 2.08/0.97  --resolution_flag                       false
% 2.08/0.97  --res_lit_sel                           adaptive
% 2.08/0.97  --res_lit_sel_side                      none
% 2.08/0.97  --res_ordering                          kbo
% 2.08/0.97  --res_to_prop_solver                    active
% 2.08/0.97  --res_prop_simpl_new                    false
% 2.08/0.97  --res_prop_simpl_given                  true
% 2.08/0.97  --res_passive_queue_type                priority_queues
% 2.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.97  --res_passive_queues_freq               [15;5]
% 2.08/0.97  --res_forward_subs                      full
% 2.08/0.97  --res_backward_subs                     full
% 2.08/0.97  --res_forward_subs_resolution           true
% 2.08/0.97  --res_backward_subs_resolution          true
% 2.08/0.97  --res_orphan_elimination                true
% 2.08/0.97  --res_time_limit                        2.
% 2.08/0.97  --res_out_proof                         true
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Options
% 2.08/0.97  
% 2.08/0.97  --superposition_flag                    true
% 2.08/0.97  --sup_passive_queue_type                priority_queues
% 2.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.97  --demod_completeness_check              fast
% 2.08/0.97  --demod_use_ground                      true
% 2.08/0.97  --sup_to_prop_solver                    passive
% 2.08/0.97  --sup_prop_simpl_new                    true
% 2.08/0.97  --sup_prop_simpl_given                  true
% 2.08/0.97  --sup_fun_splitting                     false
% 2.08/0.97  --sup_smt_interval                      50000
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Simplification Setup
% 2.08/0.97  
% 2.08/0.97  --sup_indices_passive                   []
% 2.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_full_bw                           [BwDemod]
% 2.08/0.97  --sup_immed_triv                        [TrivRules]
% 2.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_immed_bw_main                     []
% 2.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  
% 2.08/0.97  ------ Combination Options
% 2.08/0.97  
% 2.08/0.97  --comb_res_mult                         3
% 2.08/0.97  --comb_sup_mult                         2
% 2.08/0.97  --comb_inst_mult                        10
% 2.08/0.97  
% 2.08/0.97  ------ Debug Options
% 2.08/0.97  
% 2.08/0.97  --dbg_backtrace                         false
% 2.08/0.97  --dbg_dump_prop_clauses                 false
% 2.08/0.97  --dbg_dump_prop_clauses_file            -
% 2.08/0.97  --dbg_out_stat                          false
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  ------ Proving...
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  % SZS status Theorem for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97   Resolution empty clause
% 2.08/0.97  
% 2.08/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  fof(f3,axiom,(
% 2.08/0.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f11,plain,(
% 2.08/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.08/0.97    inference(ennf_transformation,[],[f3])).
% 2.08/0.97  
% 2.08/0.97  fof(f15,plain,(
% 2.08/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f16,plain,(
% 2.08/0.97    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.08/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 2.08/0.97  
% 2.08/0.97  fof(f33,plain,(
% 2.08/0.97    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f16])).
% 2.08/0.97  
% 2.08/0.97  fof(f7,axiom,(
% 2.08/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f12,plain,(
% 2.08/0.97    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.08/0.97    inference(ennf_transformation,[],[f7])).
% 2.08/0.97  
% 2.08/0.97  fof(f23,plain,(
% 2.08/0.97    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.08/0.97    inference(nnf_transformation,[],[f12])).
% 2.08/0.97  
% 2.08/0.97  fof(f41,plain,(
% 2.08/0.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f23])).
% 2.08/0.97  
% 2.08/0.97  fof(f8,conjecture,(
% 2.08/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f9,negated_conjecture,(
% 2.08/0.97    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.08/0.97    inference(negated_conjecture,[],[f8])).
% 2.08/0.97  
% 2.08/0.97  fof(f13,plain,(
% 2.08/0.97    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.08/0.97    inference(ennf_transformation,[],[f9])).
% 2.08/0.97  
% 2.08/0.97  fof(f24,plain,(
% 2.08/0.97    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.08/0.97    inference(nnf_transformation,[],[f13])).
% 2.08/0.97  
% 2.08/0.97  fof(f25,plain,(
% 2.08/0.97    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.08/0.97    inference(flattening,[],[f24])).
% 2.08/0.97  
% 2.08/0.97  fof(f26,plain,(
% 2.08/0.97    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5))),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f27,plain,(
% 2.08/0.97    (k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5)),
% 2.08/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).
% 2.08/0.97  
% 2.08/0.97  fof(f42,plain,(
% 2.08/0.97    v1_relat_1(sK5)),
% 2.08/0.97    inference(cnf_transformation,[],[f27])).
% 2.08/0.97  
% 2.08/0.97  fof(f6,axiom,(
% 2.08/0.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f17,plain,(
% 2.08/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.08/0.97    inference(nnf_transformation,[],[f6])).
% 2.08/0.97  
% 2.08/0.97  fof(f18,plain,(
% 2.08/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.08/0.97    inference(rectify,[],[f17])).
% 2.08/0.97  
% 2.08/0.97  fof(f21,plain,(
% 2.08/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f20,plain,(
% 2.08/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f19,plain,(
% 2.08/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f22,plain,(
% 2.08/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.08/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 2.08/0.97  
% 2.08/0.97  fof(f37,plain,(
% 2.08/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.08/0.97    inference(cnf_transformation,[],[f22])).
% 2.08/0.97  
% 2.08/0.97  fof(f46,plain,(
% 2.08/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.08/0.97    inference(equality_resolution,[],[f37])).
% 2.08/0.97  
% 2.08/0.97  fof(f44,plain,(
% 2.08/0.97    k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))),
% 2.08/0.97    inference(cnf_transformation,[],[f27])).
% 2.08/0.97  
% 2.08/0.97  fof(f36,plain,(
% 2.08/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.08/0.97    inference(cnf_transformation,[],[f22])).
% 2.08/0.97  
% 2.08/0.97  fof(f47,plain,(
% 2.08/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.08/0.97    inference(equality_resolution,[],[f36])).
% 2.08/0.97  
% 2.08/0.97  fof(f40,plain,(
% 2.08/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f23])).
% 2.08/0.97  
% 2.08/0.97  fof(f43,plain,(
% 2.08/0.97    k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))),
% 2.08/0.97    inference(cnf_transformation,[],[f27])).
% 2.08/0.97  
% 2.08/0.97  fof(f5,axiom,(
% 2.08/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f35,plain,(
% 2.08/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f5])).
% 2.08/0.97  
% 2.08/0.97  fof(f4,axiom,(
% 2.08/0.97    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f34,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f4])).
% 2.08/0.97  
% 2.08/0.97  fof(f45,plain,(
% 2.08/0.97    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.08/0.97    inference(definition_unfolding,[],[f35,f34])).
% 2.08/0.97  
% 2.08/0.97  fof(f2,axiom,(
% 2.08/0.97    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f10,plain,(
% 2.08/0.97    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.08/0.97    inference(ennf_transformation,[],[f2])).
% 2.08/0.97  
% 2.08/0.97  fof(f14,plain,(
% 2.08/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.08/0.97    inference(nnf_transformation,[],[f10])).
% 2.08/0.97  
% 2.08/0.97  fof(f30,plain,(
% 2.08/0.97    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.08/0.97    inference(cnf_transformation,[],[f14])).
% 2.08/0.97  
% 2.08/0.97  fof(f32,plain,(
% 2.08/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f14])).
% 2.08/0.97  
% 2.08/0.97  cnf(c_5,plain,
% 2.08/0.97      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_703,plain,
% 2.08/0.97      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_11,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.08/0.97      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.08/0.97      | ~ v1_relat_1(X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_15,negated_conjecture,
% 2.08/0.97      ( v1_relat_1(sK5) ),
% 2.08/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_211,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.08/0.97      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.08/0.97      | sK5 != X1 ),
% 2.08/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_212,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1)) | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.08/0.97      inference(unflattening,[status(thm)],[c_211]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_279,plain,
% 2.08/0.97      ( r2_hidden(k4_tarski(X1,X0),sK5) | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.08/0.97      inference(prop_impl,[status(thm)],[c_212]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_280,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1)) | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.08/0.97      inference(renaming,[status(thm)],[c_279]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_695,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(sK5,X1)) != iProver_top
% 2.08/0.97      | r2_hidden(k4_tarski(X1,X0),sK5) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1150,plain,
% 2.08/0.97      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 2.08/0.97      | r2_hidden(k4_tarski(X0,sK0(k11_relat_1(sK5,X0))),sK5) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_703,c_695]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_9,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_700,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 2.08/0.97      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4036,plain,
% 2.08/0.97      ( k11_relat_1(sK5,X0) = k1_xboole_0
% 2.08/0.97      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_1150,c_700]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_13,negated_conjecture,
% 2.08/0.97      ( ~ r2_hidden(sK4,k1_relat_1(sK5)) | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 2.08/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_698,plain,
% 2.08/0.97      ( k1_xboole_0 = k11_relat_1(sK5,sK4)
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4066,plain,
% 2.08/0.97      ( k11_relat_1(sK5,sK4) = k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_4036,c_698]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_10,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.08/0.97      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_699,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.08/0.97      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_12,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.08/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.08/0.97      | ~ v1_relat_1(X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_199,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.08/0.97      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.08/0.97      | sK5 != X1 ),
% 2.08/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_200,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(sK5,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.08/0.97      inference(unflattening,[status(thm)],[c_199]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_281,plain,
% 2.08/0.97      ( ~ r2_hidden(k4_tarski(X1,X0),sK5) | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.08/0.97      inference(prop_impl,[status(thm)],[c_200]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_282,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(sK5,X1)) | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.08/0.97      inference(renaming,[status(thm)],[c_281]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_696,plain,
% 2.08/0.97      ( r2_hidden(X0,k11_relat_1(sK5,X1)) = iProver_top
% 2.08/0.97      | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1132,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.08/0.97      | r2_hidden(sK3(sK5,X0),k11_relat_1(sK5,X0)) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_699,c_696]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4188,plain,
% 2.08/0.97      ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_4066,c_1132]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_18,plain,
% 2.08/0.97      ( k1_xboole_0 = k11_relat_1(sK5,sK4)
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_862,plain,
% 2.08/0.97      ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
% 2.08/0.97      | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_863,plain,
% 2.08/0.97      ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) = iProver_top
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_884,plain,
% 2.08/0.97      ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.08/0.97      | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_282]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_885,plain,
% 2.08/0.97      ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4)) = iProver_top
% 2.08/0.97      | r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_884]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_368,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.08/0.97      theory(equality) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1046,plain,
% 2.08/0.97      ( r2_hidden(X0,X1)
% 2.08/0.97      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.08/0.97      | X1 != k11_relat_1(sK5,sK4)
% 2.08/0.97      | X0 != sK3(sK5,sK4) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_368]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2391,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_xboole_0)
% 2.08/0.97      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.08/0.97      | X0 != sK3(sK5,sK4)
% 2.08/0.97      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_1046]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2800,plain,
% 2.08/0.97      ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.08/0.97      | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
% 2.08/0.97      | sK3(sK5,sK4) != sK3(sK5,sK4)
% 2.08/0.97      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_2391]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2802,plain,
% 2.08/0.97      ( sK3(sK5,sK4) != sK3(sK5,sK4)
% 2.08/0.97      | k1_xboole_0 != k11_relat_1(sK5,sK4)
% 2.08/0.97      | r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4)) != iProver_top
% 2.08/0.97      | r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_2800]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_364,plain,( X0 = X0 ),theory(equality) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2801,plain,
% 2.08/0.97      ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_364]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_14,negated_conjecture,
% 2.08/0.97      ( r2_hidden(sK4,k1_relat_1(sK5)) | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.08/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_697,plain,
% 2.08/0.97      ( k1_xboole_0 != k11_relat_1(sK5,sK4)
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4177,plain,
% 2.08/0.97      ( k1_xboole_0 != k1_xboole_0
% 2.08/0.97      | r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
% 2.08/0.97      inference(demodulation,[status(thm)],[c_4066,c_697]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4178,plain,
% 2.08/0.97      ( r2_hidden(sK4,k1_relat_1(sK5)) = iProver_top ),
% 2.08/0.97      inference(equality_resolution_simp,[status(thm)],[c_4177]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4499,plain,
% 2.08/0.97      ( r2_hidden(sK3(sK5,sK4),k1_xboole_0) = iProver_top ),
% 2.08/0.97      inference(global_propositional_subsumption,
% 2.08/0.97                [status(thm)],
% 2.08/0.97                [c_4188,c_18,c_863,c_885,c_2802,c_2801,c_4178]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_6,plain,
% 2.08/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,X1)
% 2.08/0.97      | ~ r2_hidden(X0,X2)
% 2.08/0.97      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 2.08/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_705,plain,
% 2.08/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.08/0.97      | r2_hidden(X0,X2) != iProver_top
% 2.08/0.97      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2683,plain,
% 2.08/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.08/0.97      | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_6,c_705]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1,plain,
% 2.08/0.97      ( ~ r2_hidden(X0,X1)
% 2.08/0.97      | r2_hidden(X0,X2)
% 2.08/0.97      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 2.08/0.97      inference(cnf_transformation,[],[f32]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_707,plain,
% 2.08/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.08/0.97      | r2_hidden(X0,X2) = iProver_top
% 2.08/0.97      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1504,plain,
% 2.08/0.97      ( r2_hidden(X0,X1) = iProver_top
% 2.08/0.97      | r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_6,c_707]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2835,plain,
% 2.08/0.97      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 2.08/0.97      inference(global_propositional_subsumption,[status(thm)],[c_2683,c_1504]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2842,plain,
% 2.08/0.97      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_703,c_2835]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2867,plain,
% 2.08/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.08/0.97      inference(demodulation,[status(thm)],[c_2842,c_2835]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4504,plain,
% 2.08/0.97      ( $false ),
% 2.08/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_4499,c_2867]) ).
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  ------                               Statistics
% 2.08/0.97  
% 2.08/0.97  ------ General
% 2.08/0.97  
% 2.08/0.97  abstr_ref_over_cycles:                  0
% 2.08/0.97  abstr_ref_under_cycles:                 0
% 2.08/0.97  gc_basic_clause_elim:                   0
% 2.08/0.97  forced_gc_time:                         0
% 2.08/0.97  parsing_time:                           0.01
% 2.08/0.97  unif_index_cands_time:                  0.
% 2.08/0.97  unif_index_add_time:                    0.
% 2.08/0.97  orderings_time:                         0.
% 2.08/0.97  out_proof_time:                         0.007
% 2.08/0.97  total_time:                             0.156
% 2.08/0.97  num_of_symbols:                         45
% 2.08/0.97  num_of_terms:                           4722
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing
% 2.08/0.97  
% 2.08/0.97  num_of_splits:                          0
% 2.08/0.97  num_of_split_atoms:                     0
% 2.08/0.97  num_of_reused_defs:                     0
% 2.08/0.97  num_eq_ax_congr_red:                    27
% 2.08/0.97  num_of_sem_filtered_clauses:            1
% 2.08/0.97  num_of_subtypes:                        0
% 2.08/0.97  monotx_restored_types:                  0
% 2.08/0.97  sat_num_of_epr_types:                   0
% 2.08/0.97  sat_num_of_non_cyclic_types:            0
% 2.08/0.97  sat_guarded_non_collapsed_types:        0
% 2.08/0.97  num_pure_diseq_elim:                    0
% 2.08/0.97  simp_replaced_by:                       0
% 2.08/0.97  res_preprocessed:                       78
% 2.08/0.97  prep_upred:                             0
% 2.08/0.97  prep_unflattend:                        2
% 2.08/0.97  smt_new_axioms:                         0
% 2.08/0.97  pred_elim_cands:                        1
% 2.08/0.97  pred_elim:                              1
% 2.08/0.97  pred_elim_cl:                           1
% 2.08/0.97  pred_elim_cycles:                       3
% 2.08/0.97  merged_defs:                            14
% 2.08/0.97  merged_defs_ncl:                        0
% 2.08/0.97  bin_hyper_res:                          14
% 2.08/0.97  prep_cycles:                            4
% 2.08/0.97  pred_elim_time:                         0.
% 2.08/0.97  splitting_time:                         0.
% 2.08/0.97  sem_filter_time:                        0.
% 2.08/0.97  monotx_time:                            0.
% 2.08/0.97  subtype_inf_time:                       0.
% 2.08/0.97  
% 2.08/0.97  ------ Problem properties
% 2.08/0.97  
% 2.08/0.97  clauses:                                15
% 2.08/0.97  conjectures:                            2
% 2.08/0.97  epr:                                    0
% 2.08/0.97  horn:                                   10
% 2.08/0.97  ground:                                 2
% 2.08/0.97  unary:                                  2
% 2.08/0.97  binary:                                 7
% 2.08/0.97  lits:                                   34
% 2.08/0.97  lits_eq:                                7
% 2.08/0.97  fd_pure:                                0
% 2.08/0.97  fd_pseudo:                              0
% 2.08/0.97  fd_cond:                                1
% 2.08/0.97  fd_pseudo_cond:                         2
% 2.08/0.97  ac_symbols:                             0
% 2.08/0.97  
% 2.08/0.97  ------ Propositional Solver
% 2.08/0.97  
% 2.08/0.97  prop_solver_calls:                      27
% 2.08/0.97  prop_fast_solver_calls:                 461
% 2.08/0.97  smt_solver_calls:                       0
% 2.08/0.97  smt_fast_solver_calls:                  0
% 2.08/0.97  prop_num_of_clauses:                    1791
% 2.08/0.97  prop_preprocess_simplified:             4488
% 2.08/0.97  prop_fo_subsumed:                       4
% 2.08/0.97  prop_solver_time:                       0.
% 2.08/0.97  smt_solver_time:                        0.
% 2.08/0.97  smt_fast_solver_time:                   0.
% 2.08/0.97  prop_fast_solver_time:                  0.
% 2.08/0.97  prop_unsat_core_time:                   0.
% 2.08/0.97  
% 2.08/0.97  ------ QBF
% 2.08/0.97  
% 2.08/0.97  qbf_q_res:                              0
% 2.08/0.97  qbf_num_tautologies:                    0
% 2.08/0.97  qbf_prep_cycles:                        0
% 2.08/0.97  
% 2.08/0.97  ------ BMC1
% 2.08/0.97  
% 2.08/0.97  bmc1_current_bound:                     -1
% 2.08/0.97  bmc1_last_solved_bound:                 -1
% 2.08/0.97  bmc1_unsat_core_size:                   -1
% 2.08/0.97  bmc1_unsat_core_parents_size:           -1
% 2.08/0.97  bmc1_merge_next_fun:                    0
% 2.08/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation
% 2.08/0.97  
% 2.08/0.97  inst_num_of_clauses:                    433
% 2.08/0.97  inst_num_in_passive:                    50
% 2.08/0.97  inst_num_in_active:                     181
% 2.08/0.97  inst_num_in_unprocessed:                202
% 2.08/0.97  inst_num_of_loops:                      220
% 2.08/0.97  inst_num_of_learning_restarts:          0
% 2.08/0.97  inst_num_moves_active_passive:          37
% 2.08/0.97  inst_lit_activity:                      0
% 2.08/0.97  inst_lit_activity_moves:                0
% 2.08/0.97  inst_num_tautologies:                   0
% 2.08/0.97  inst_num_prop_implied:                  0
% 2.08/0.97  inst_num_existing_simplified:           0
% 2.08/0.97  inst_num_eq_res_simplified:             0
% 2.08/0.97  inst_num_child_elim:                    0
% 2.08/0.97  inst_num_of_dismatching_blockings:      163
% 2.08/0.97  inst_num_of_non_proper_insts:           350
% 2.08/0.97  inst_num_of_duplicates:                 0
% 2.08/0.97  inst_inst_num_from_inst_to_res:         0
% 2.08/0.97  inst_dismatching_checking_time:         0.
% 2.08/0.97  
% 2.08/0.97  ------ Resolution
% 2.08/0.97  
% 2.08/0.97  res_num_of_clauses:                     0
% 2.08/0.97  res_num_in_passive:                     0
% 2.08/0.97  res_num_in_active:                      0
% 2.08/0.97  res_num_of_loops:                       82
% 2.08/0.97  res_forward_subset_subsumed:            8
% 2.08/0.97  res_backward_subset_subsumed:           0
% 2.08/0.97  res_forward_subsumed:                   0
% 2.08/0.97  res_backward_subsumed:                  0
% 2.08/0.97  res_forward_subsumption_resolution:     0
% 2.08/0.97  res_backward_subsumption_resolution:    0
% 2.08/0.97  res_clause_to_clause_subsumption:       389
% 2.08/0.97  res_orphan_elimination:                 0
% 2.08/0.97  res_tautology_del:                      58
% 2.08/0.97  res_num_eq_res_simplified:              0
% 2.08/0.97  res_num_sel_changes:                    0
% 2.08/0.97  res_moves_from_active_to_pass:          0
% 2.08/0.97  
% 2.08/0.97  ------ Superposition
% 2.08/0.97  
% 2.08/0.97  sup_time_total:                         0.
% 2.08/0.97  sup_time_generating:                    0.
% 2.08/0.97  sup_time_sim_full:                      0.
% 2.08/0.97  sup_time_sim_immed:                     0.
% 2.08/0.97  
% 2.08/0.97  sup_num_of_clauses:                     103
% 2.08/0.97  sup_num_in_active:                      28
% 2.08/0.97  sup_num_in_passive:                     75
% 2.08/0.97  sup_num_of_loops:                       42
% 2.08/0.97  sup_fw_superposition:                   85
% 2.08/0.97  sup_bw_superposition:                   79
% 2.08/0.97  sup_immediate_simplified:               17
% 2.08/0.97  sup_given_eliminated:                   2
% 2.08/0.97  comparisons_done:                       0
% 2.08/0.97  comparisons_avoided:                    0
% 2.08/0.97  
% 2.08/0.97  ------ Simplifications
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  sim_fw_subset_subsumed:                 7
% 2.08/0.97  sim_bw_subset_subsumed:                 7
% 2.08/0.97  sim_fw_subsumed:                        7
% 2.08/0.97  sim_bw_subsumed:                        3
% 2.08/0.97  sim_fw_subsumption_res:                 1
% 2.08/0.97  sim_bw_subsumption_res:                 0
% 2.08/0.97  sim_tautology_del:                      13
% 2.08/0.97  sim_eq_tautology_del:                   2
% 2.08/0.97  sim_eq_res_simp:                        1
% 2.08/0.97  sim_fw_demodulated:                     6
% 2.08/0.97  sim_bw_demodulated:                     17
% 2.08/0.97  sim_light_normalised:                   3
% 2.08/0.97  sim_joinable_taut:                      0
% 2.08/0.97  sim_joinable_simp:                      0
% 2.08/0.97  sim_ac_normalised:                      0
% 2.08/0.97  sim_smt_subsumption:                    0
% 2.08/0.97  
%------------------------------------------------------------------------------
