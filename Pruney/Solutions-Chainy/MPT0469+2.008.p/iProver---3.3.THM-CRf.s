%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:43 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 357 expanded)
%              Number of clauses        :   91 ( 154 expanded)
%              Number of leaves         :   20 (  81 expanded)
%              Depth                    :   19
%              Number of atoms          :  365 (1005 expanded)
%              Number of equality atoms :  164 ( 274 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_949,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_955,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_946,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1113,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_946])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_938,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1237,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1113,c_938])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_940,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2435,plain,
    ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_940])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_36,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_49,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_51,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_72,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10806,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2435,c_36,c_51,c_72])).

cnf(c_10807,plain,
    ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10806])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_957,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_942,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_951,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1440,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_949,c_951])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_948,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1444,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_948])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_954,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2522,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_954])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_330,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_3290,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2522,c_330])).

cnf(c_3299,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_3290])).

cnf(c_3390,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_3299])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_952,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_956,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1733,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_956])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_947,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1907,plain,
    ( k4_xboole_0(X0,X1) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_947])).

cnf(c_3417,plain,
    ( k4_xboole_0(k1_relat_1(k1_xboole_0),X0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3390,c_1907])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_950,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3695,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_950])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_44,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1477,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1484,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1750,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1757,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_6828,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3695,c_44,c_2,c_1484,c_1757])).

cnf(c_6835,plain,
    ( k4_xboole_0(k1_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6828,c_951])).

cnf(c_6838,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6835,c_3417])).

cnf(c_10812,plain,
    ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10807,c_6838])).

cnf(c_10819,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_10812])).

cnf(c_3006,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3013,plain,
    ( ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_1392,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1393,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_1395,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1293,plain,
    ( r1_xboole_0(k2_relat_1(k1_xboole_0),X0)
    | r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1300,plain,
    ( r1_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK1(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_415,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1250,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1251,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1231,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),X0) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1232,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1106,plain,
    ( k2_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1200,plain,
    ( k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
    | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_1201,plain,
    ( k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1136,plain,
    ( ~ r1_xboole_0(k2_relat_1(k1_xboole_0),X0)
    | k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1139,plain,
    ( ~ r1_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1121,plain,
    ( X0 != X1
    | k2_relat_1(k1_xboole_0) != X1
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1126,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = X0
    | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1135,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
    | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1137,plain,
    ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_414,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_431,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_422,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_429,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10819,c_3013,c_1757,c_1484,c_1395,c_1300,c_1251,c_1232,c_1201,c_1139,c_1137,c_431,c_429,c_72,c_2,c_51,c_44,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.72/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.97  
% 2.72/0.97  ------  iProver source info
% 2.72/0.97  
% 2.72/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.97  git: non_committed_changes: false
% 2.72/0.97  git: last_make_outside_of_git: false
% 2.72/0.97  
% 2.72/0.97  ------ 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options
% 2.72/0.97  
% 2.72/0.97  --out_options                           all
% 2.72/0.97  --tptp_safe_out                         true
% 2.72/0.97  --problem_path                          ""
% 2.72/0.97  --include_path                          ""
% 2.72/0.97  --clausifier                            res/vclausify_rel
% 2.72/0.97  --clausifier_options                    --mode clausify
% 2.72/0.97  --stdin                                 false
% 2.72/0.97  --stats_out                             all
% 2.72/0.97  
% 2.72/0.97  ------ General Options
% 2.72/0.97  
% 2.72/0.97  --fof                                   false
% 2.72/0.97  --time_out_real                         305.
% 2.72/0.97  --time_out_virtual                      -1.
% 2.72/0.97  --symbol_type_check                     false
% 2.72/0.97  --clausify_out                          false
% 2.72/0.97  --sig_cnt_out                           false
% 2.72/0.97  --trig_cnt_out                          false
% 2.72/0.97  --trig_cnt_out_tolerance                1.
% 2.72/0.97  --trig_cnt_out_sk_spl                   false
% 2.72/0.97  --abstr_cl_out                          false
% 2.72/0.97  
% 2.72/0.97  ------ Global Options
% 2.72/0.97  
% 2.72/0.97  --schedule                              default
% 2.72/0.97  --add_important_lit                     false
% 2.72/0.97  --prop_solver_per_cl                    1000
% 2.72/0.97  --min_unsat_core                        false
% 2.72/0.97  --soft_assumptions                      false
% 2.72/0.97  --soft_lemma_size                       3
% 2.72/0.97  --prop_impl_unit_size                   0
% 2.72/0.97  --prop_impl_unit                        []
% 2.72/0.97  --share_sel_clauses                     true
% 2.72/0.97  --reset_solvers                         false
% 2.72/0.97  --bc_imp_inh                            [conj_cone]
% 2.72/0.97  --conj_cone_tolerance                   3.
% 2.72/0.97  --extra_neg_conj                        none
% 2.72/0.97  --large_theory_mode                     true
% 2.72/0.97  --prolific_symb_bound                   200
% 2.72/0.97  --lt_threshold                          2000
% 2.72/0.97  --clause_weak_htbl                      true
% 2.72/0.97  --gc_record_bc_elim                     false
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing Options
% 2.72/0.97  
% 2.72/0.97  --preprocessing_flag                    true
% 2.72/0.97  --time_out_prep_mult                    0.1
% 2.72/0.97  --splitting_mode                        input
% 2.72/0.97  --splitting_grd                         true
% 2.72/0.97  --splitting_cvd                         false
% 2.72/0.97  --splitting_cvd_svl                     false
% 2.72/0.97  --splitting_nvd                         32
% 2.72/0.97  --sub_typing                            true
% 2.72/0.97  --prep_gs_sim                           true
% 2.72/0.97  --prep_unflatten                        true
% 2.72/0.97  --prep_res_sim                          true
% 2.72/0.97  --prep_upred                            true
% 2.72/0.97  --prep_sem_filter                       exhaustive
% 2.72/0.97  --prep_sem_filter_out                   false
% 2.72/0.97  --pred_elim                             true
% 2.72/0.97  --res_sim_input                         true
% 2.72/0.97  --eq_ax_congr_red                       true
% 2.72/0.97  --pure_diseq_elim                       true
% 2.72/0.97  --brand_transform                       false
% 2.72/0.97  --non_eq_to_eq                          false
% 2.72/0.97  --prep_def_merge                        true
% 2.72/0.97  --prep_def_merge_prop_impl              false
% 2.72/0.97  --prep_def_merge_mbd                    true
% 2.72/0.97  --prep_def_merge_tr_red                 false
% 2.72/0.97  --prep_def_merge_tr_cl                  false
% 2.72/0.97  --smt_preprocessing                     true
% 2.72/0.97  --smt_ac_axioms                         fast
% 2.72/0.97  --preprocessed_out                      false
% 2.72/0.97  --preprocessed_stats                    false
% 2.72/0.97  
% 2.72/0.97  ------ Abstraction refinement Options
% 2.72/0.97  
% 2.72/0.97  --abstr_ref                             []
% 2.72/0.97  --abstr_ref_prep                        false
% 2.72/0.97  --abstr_ref_until_sat                   false
% 2.72/0.97  --abstr_ref_sig_restrict                funpre
% 2.72/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.97  --abstr_ref_under                       []
% 2.72/0.97  
% 2.72/0.97  ------ SAT Options
% 2.72/0.97  
% 2.72/0.97  --sat_mode                              false
% 2.72/0.97  --sat_fm_restart_options                ""
% 2.72/0.97  --sat_gr_def                            false
% 2.72/0.97  --sat_epr_types                         true
% 2.72/0.97  --sat_non_cyclic_types                  false
% 2.72/0.97  --sat_finite_models                     false
% 2.72/0.97  --sat_fm_lemmas                         false
% 2.72/0.97  --sat_fm_prep                           false
% 2.72/0.97  --sat_fm_uc_incr                        true
% 2.72/0.97  --sat_out_model                         small
% 2.72/0.97  --sat_out_clauses                       false
% 2.72/0.97  
% 2.72/0.97  ------ QBF Options
% 2.72/0.97  
% 2.72/0.97  --qbf_mode                              false
% 2.72/0.97  --qbf_elim_univ                         false
% 2.72/0.97  --qbf_dom_inst                          none
% 2.72/0.97  --qbf_dom_pre_inst                      false
% 2.72/0.97  --qbf_sk_in                             false
% 2.72/0.97  --qbf_pred_elim                         true
% 2.72/0.97  --qbf_split                             512
% 2.72/0.97  
% 2.72/0.97  ------ BMC1 Options
% 2.72/0.97  
% 2.72/0.97  --bmc1_incremental                      false
% 2.72/0.97  --bmc1_axioms                           reachable_all
% 2.72/0.97  --bmc1_min_bound                        0
% 2.72/0.97  --bmc1_max_bound                        -1
% 2.72/0.97  --bmc1_max_bound_default                -1
% 2.72/0.97  --bmc1_symbol_reachability              true
% 2.72/0.97  --bmc1_property_lemmas                  false
% 2.72/0.97  --bmc1_k_induction                      false
% 2.72/0.97  --bmc1_non_equiv_states                 false
% 2.72/0.97  --bmc1_deadlock                         false
% 2.72/0.97  --bmc1_ucm                              false
% 2.72/0.97  --bmc1_add_unsat_core                   none
% 2.72/0.97  --bmc1_unsat_core_children              false
% 2.72/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.97  --bmc1_out_stat                         full
% 2.72/0.97  --bmc1_ground_init                      false
% 2.72/0.97  --bmc1_pre_inst_next_state              false
% 2.72/0.97  --bmc1_pre_inst_state                   false
% 2.72/0.97  --bmc1_pre_inst_reach_state             false
% 2.72/0.97  --bmc1_out_unsat_core                   false
% 2.72/0.97  --bmc1_aig_witness_out                  false
% 2.72/0.97  --bmc1_verbose                          false
% 2.72/0.97  --bmc1_dump_clauses_tptp                false
% 2.72/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.97  --bmc1_dump_file                        -
% 2.72/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.97  --bmc1_ucm_extend_mode                  1
% 2.72/0.97  --bmc1_ucm_init_mode                    2
% 2.72/0.97  --bmc1_ucm_cone_mode                    none
% 2.72/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.97  --bmc1_ucm_relax_model                  4
% 2.72/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.97  --bmc1_ucm_layered_model                none
% 2.72/0.97  --bmc1_ucm_max_lemma_size               10
% 2.72/0.97  
% 2.72/0.97  ------ AIG Options
% 2.72/0.97  
% 2.72/0.97  --aig_mode                              false
% 2.72/0.97  
% 2.72/0.97  ------ Instantiation Options
% 2.72/0.97  
% 2.72/0.97  --instantiation_flag                    true
% 2.72/0.97  --inst_sos_flag                         false
% 2.72/0.97  --inst_sos_phase                        true
% 2.72/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel_side                     num_symb
% 2.72/0.97  --inst_solver_per_active                1400
% 2.72/0.97  --inst_solver_calls_frac                1.
% 2.72/0.97  --inst_passive_queue_type               priority_queues
% 2.72/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.97  --inst_passive_queues_freq              [25;2]
% 2.72/0.97  --inst_dismatching                      true
% 2.72/0.97  --inst_eager_unprocessed_to_passive     true
% 2.72/0.97  --inst_prop_sim_given                   true
% 2.72/0.97  --inst_prop_sim_new                     false
% 2.72/0.97  --inst_subs_new                         false
% 2.72/0.97  --inst_eq_res_simp                      false
% 2.72/0.97  --inst_subs_given                       false
% 2.72/0.97  --inst_orphan_elimination               true
% 2.72/0.97  --inst_learning_loop_flag               true
% 2.72/0.97  --inst_learning_start                   3000
% 2.72/0.97  --inst_learning_factor                  2
% 2.72/0.97  --inst_start_prop_sim_after_learn       3
% 2.72/0.97  --inst_sel_renew                        solver
% 2.72/0.97  --inst_lit_activity_flag                true
% 2.72/0.97  --inst_restr_to_given                   false
% 2.72/0.97  --inst_activity_threshold               500
% 2.72/0.97  --inst_out_proof                        true
% 2.72/0.97  
% 2.72/0.97  ------ Resolution Options
% 2.72/0.97  
% 2.72/0.97  --resolution_flag                       true
% 2.72/0.97  --res_lit_sel                           adaptive
% 2.72/0.97  --res_lit_sel_side                      none
% 2.72/0.97  --res_ordering                          kbo
% 2.72/0.97  --res_to_prop_solver                    active
% 2.72/0.97  --res_prop_simpl_new                    false
% 2.72/0.97  --res_prop_simpl_given                  true
% 2.72/0.97  --res_passive_queue_type                priority_queues
% 2.72/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.97  --res_passive_queues_freq               [15;5]
% 2.72/0.97  --res_forward_subs                      full
% 2.72/0.97  --res_backward_subs                     full
% 2.72/0.97  --res_forward_subs_resolution           true
% 2.72/0.97  --res_backward_subs_resolution          true
% 2.72/0.97  --res_orphan_elimination                true
% 2.72/0.97  --res_time_limit                        2.
% 2.72/0.97  --res_out_proof                         true
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Options
% 2.72/0.97  
% 2.72/0.97  --superposition_flag                    true
% 2.72/0.97  --sup_passive_queue_type                priority_queues
% 2.72/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.97  --demod_completeness_check              fast
% 2.72/0.97  --demod_use_ground                      true
% 2.72/0.97  --sup_to_prop_solver                    passive
% 2.72/0.97  --sup_prop_simpl_new                    true
% 2.72/0.97  --sup_prop_simpl_given                  true
% 2.72/0.97  --sup_fun_splitting                     false
% 2.72/0.97  --sup_smt_interval                      50000
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Simplification Setup
% 2.72/0.97  
% 2.72/0.97  --sup_indices_passive                   []
% 2.72/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_full_bw                           [BwDemod]
% 2.72/0.97  --sup_immed_triv                        [TrivRules]
% 2.72/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_immed_bw_main                     []
% 2.72/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  
% 2.72/0.97  ------ Combination Options
% 2.72/0.97  
% 2.72/0.97  --comb_res_mult                         3
% 2.72/0.97  --comb_sup_mult                         2
% 2.72/0.97  --comb_inst_mult                        10
% 2.72/0.97  
% 2.72/0.97  ------ Debug Options
% 2.72/0.97  
% 2.72/0.97  --dbg_backtrace                         false
% 2.72/0.97  --dbg_dump_prop_clauses                 false
% 2.72/0.97  --dbg_dump_prop_clauses_file            -
% 2.72/0.97  --dbg_out_stat                          false
% 2.72/0.97  ------ Parsing...
% 2.72/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.97  ------ Proving...
% 2.72/0.97  ------ Problem Properties 
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  clauses                                 22
% 2.72/0.97  conjectures                             1
% 2.72/0.97  EPR                                     5
% 2.72/0.97  Horn                                    18
% 2.72/0.97  unary                                   2
% 2.72/0.97  binary                                  15
% 2.72/0.97  lits                                    49
% 2.72/0.97  lits eq                                 10
% 2.72/0.97  fd_pure                                 0
% 2.72/0.97  fd_pseudo                               0
% 2.72/0.97  fd_cond                                 0
% 2.72/0.97  fd_pseudo_cond                          2
% 2.72/0.97  AC symbols                              0
% 2.72/0.97  
% 2.72/0.97  ------ Schedule dynamic 5 is on 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  ------ 
% 2.72/0.97  Current options:
% 2.72/0.97  ------ 
% 2.72/0.97  
% 2.72/0.97  ------ Input Options
% 2.72/0.97  
% 2.72/0.97  --out_options                           all
% 2.72/0.97  --tptp_safe_out                         true
% 2.72/0.97  --problem_path                          ""
% 2.72/0.97  --include_path                          ""
% 2.72/0.97  --clausifier                            res/vclausify_rel
% 2.72/0.97  --clausifier_options                    --mode clausify
% 2.72/0.97  --stdin                                 false
% 2.72/0.97  --stats_out                             all
% 2.72/0.97  
% 2.72/0.97  ------ General Options
% 2.72/0.97  
% 2.72/0.97  --fof                                   false
% 2.72/0.97  --time_out_real                         305.
% 2.72/0.97  --time_out_virtual                      -1.
% 2.72/0.97  --symbol_type_check                     false
% 2.72/0.97  --clausify_out                          false
% 2.72/0.97  --sig_cnt_out                           false
% 2.72/0.97  --trig_cnt_out                          false
% 2.72/0.97  --trig_cnt_out_tolerance                1.
% 2.72/0.97  --trig_cnt_out_sk_spl                   false
% 2.72/0.97  --abstr_cl_out                          false
% 2.72/0.97  
% 2.72/0.97  ------ Global Options
% 2.72/0.97  
% 2.72/0.97  --schedule                              default
% 2.72/0.97  --add_important_lit                     false
% 2.72/0.97  --prop_solver_per_cl                    1000
% 2.72/0.97  --min_unsat_core                        false
% 2.72/0.97  --soft_assumptions                      false
% 2.72/0.97  --soft_lemma_size                       3
% 2.72/0.97  --prop_impl_unit_size                   0
% 2.72/0.97  --prop_impl_unit                        []
% 2.72/0.97  --share_sel_clauses                     true
% 2.72/0.97  --reset_solvers                         false
% 2.72/0.97  --bc_imp_inh                            [conj_cone]
% 2.72/0.97  --conj_cone_tolerance                   3.
% 2.72/0.97  --extra_neg_conj                        none
% 2.72/0.97  --large_theory_mode                     true
% 2.72/0.97  --prolific_symb_bound                   200
% 2.72/0.97  --lt_threshold                          2000
% 2.72/0.97  --clause_weak_htbl                      true
% 2.72/0.97  --gc_record_bc_elim                     false
% 2.72/0.97  
% 2.72/0.97  ------ Preprocessing Options
% 2.72/0.97  
% 2.72/0.97  --preprocessing_flag                    true
% 2.72/0.97  --time_out_prep_mult                    0.1
% 2.72/0.97  --splitting_mode                        input
% 2.72/0.97  --splitting_grd                         true
% 2.72/0.97  --splitting_cvd                         false
% 2.72/0.97  --splitting_cvd_svl                     false
% 2.72/0.97  --splitting_nvd                         32
% 2.72/0.97  --sub_typing                            true
% 2.72/0.97  --prep_gs_sim                           true
% 2.72/0.97  --prep_unflatten                        true
% 2.72/0.97  --prep_res_sim                          true
% 2.72/0.97  --prep_upred                            true
% 2.72/0.97  --prep_sem_filter                       exhaustive
% 2.72/0.97  --prep_sem_filter_out                   false
% 2.72/0.97  --pred_elim                             true
% 2.72/0.97  --res_sim_input                         true
% 2.72/0.97  --eq_ax_congr_red                       true
% 2.72/0.97  --pure_diseq_elim                       true
% 2.72/0.97  --brand_transform                       false
% 2.72/0.97  --non_eq_to_eq                          false
% 2.72/0.97  --prep_def_merge                        true
% 2.72/0.97  --prep_def_merge_prop_impl              false
% 2.72/0.97  --prep_def_merge_mbd                    true
% 2.72/0.97  --prep_def_merge_tr_red                 false
% 2.72/0.97  --prep_def_merge_tr_cl                  false
% 2.72/0.97  --smt_preprocessing                     true
% 2.72/0.97  --smt_ac_axioms                         fast
% 2.72/0.97  --preprocessed_out                      false
% 2.72/0.97  --preprocessed_stats                    false
% 2.72/0.97  
% 2.72/0.97  ------ Abstraction refinement Options
% 2.72/0.97  
% 2.72/0.97  --abstr_ref                             []
% 2.72/0.97  --abstr_ref_prep                        false
% 2.72/0.97  --abstr_ref_until_sat                   false
% 2.72/0.97  --abstr_ref_sig_restrict                funpre
% 2.72/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.97  --abstr_ref_under                       []
% 2.72/0.97  
% 2.72/0.97  ------ SAT Options
% 2.72/0.97  
% 2.72/0.97  --sat_mode                              false
% 2.72/0.97  --sat_fm_restart_options                ""
% 2.72/0.97  --sat_gr_def                            false
% 2.72/0.97  --sat_epr_types                         true
% 2.72/0.97  --sat_non_cyclic_types                  false
% 2.72/0.97  --sat_finite_models                     false
% 2.72/0.97  --sat_fm_lemmas                         false
% 2.72/0.97  --sat_fm_prep                           false
% 2.72/0.97  --sat_fm_uc_incr                        true
% 2.72/0.97  --sat_out_model                         small
% 2.72/0.97  --sat_out_clauses                       false
% 2.72/0.97  
% 2.72/0.97  ------ QBF Options
% 2.72/0.97  
% 2.72/0.97  --qbf_mode                              false
% 2.72/0.97  --qbf_elim_univ                         false
% 2.72/0.97  --qbf_dom_inst                          none
% 2.72/0.97  --qbf_dom_pre_inst                      false
% 2.72/0.97  --qbf_sk_in                             false
% 2.72/0.97  --qbf_pred_elim                         true
% 2.72/0.97  --qbf_split                             512
% 2.72/0.97  
% 2.72/0.97  ------ BMC1 Options
% 2.72/0.97  
% 2.72/0.97  --bmc1_incremental                      false
% 2.72/0.97  --bmc1_axioms                           reachable_all
% 2.72/0.97  --bmc1_min_bound                        0
% 2.72/0.97  --bmc1_max_bound                        -1
% 2.72/0.97  --bmc1_max_bound_default                -1
% 2.72/0.97  --bmc1_symbol_reachability              true
% 2.72/0.97  --bmc1_property_lemmas                  false
% 2.72/0.97  --bmc1_k_induction                      false
% 2.72/0.97  --bmc1_non_equiv_states                 false
% 2.72/0.97  --bmc1_deadlock                         false
% 2.72/0.97  --bmc1_ucm                              false
% 2.72/0.97  --bmc1_add_unsat_core                   none
% 2.72/0.97  --bmc1_unsat_core_children              false
% 2.72/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.97  --bmc1_out_stat                         full
% 2.72/0.97  --bmc1_ground_init                      false
% 2.72/0.97  --bmc1_pre_inst_next_state              false
% 2.72/0.97  --bmc1_pre_inst_state                   false
% 2.72/0.97  --bmc1_pre_inst_reach_state             false
% 2.72/0.97  --bmc1_out_unsat_core                   false
% 2.72/0.97  --bmc1_aig_witness_out                  false
% 2.72/0.97  --bmc1_verbose                          false
% 2.72/0.97  --bmc1_dump_clauses_tptp                false
% 2.72/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.97  --bmc1_dump_file                        -
% 2.72/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.97  --bmc1_ucm_extend_mode                  1
% 2.72/0.97  --bmc1_ucm_init_mode                    2
% 2.72/0.97  --bmc1_ucm_cone_mode                    none
% 2.72/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.97  --bmc1_ucm_relax_model                  4
% 2.72/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.97  --bmc1_ucm_layered_model                none
% 2.72/0.97  --bmc1_ucm_max_lemma_size               10
% 2.72/0.97  
% 2.72/0.97  ------ AIG Options
% 2.72/0.97  
% 2.72/0.97  --aig_mode                              false
% 2.72/0.97  
% 2.72/0.97  ------ Instantiation Options
% 2.72/0.97  
% 2.72/0.97  --instantiation_flag                    true
% 2.72/0.97  --inst_sos_flag                         false
% 2.72/0.97  --inst_sos_phase                        true
% 2.72/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.97  --inst_lit_sel_side                     none
% 2.72/0.97  --inst_solver_per_active                1400
% 2.72/0.97  --inst_solver_calls_frac                1.
% 2.72/0.97  --inst_passive_queue_type               priority_queues
% 2.72/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.97  --inst_passive_queues_freq              [25;2]
% 2.72/0.97  --inst_dismatching                      true
% 2.72/0.97  --inst_eager_unprocessed_to_passive     true
% 2.72/0.97  --inst_prop_sim_given                   true
% 2.72/0.97  --inst_prop_sim_new                     false
% 2.72/0.97  --inst_subs_new                         false
% 2.72/0.97  --inst_eq_res_simp                      false
% 2.72/0.97  --inst_subs_given                       false
% 2.72/0.97  --inst_orphan_elimination               true
% 2.72/0.97  --inst_learning_loop_flag               true
% 2.72/0.97  --inst_learning_start                   3000
% 2.72/0.97  --inst_learning_factor                  2
% 2.72/0.97  --inst_start_prop_sim_after_learn       3
% 2.72/0.97  --inst_sel_renew                        solver
% 2.72/0.97  --inst_lit_activity_flag                true
% 2.72/0.97  --inst_restr_to_given                   false
% 2.72/0.97  --inst_activity_threshold               500
% 2.72/0.97  --inst_out_proof                        true
% 2.72/0.97  
% 2.72/0.97  ------ Resolution Options
% 2.72/0.97  
% 2.72/0.97  --resolution_flag                       false
% 2.72/0.97  --res_lit_sel                           adaptive
% 2.72/0.97  --res_lit_sel_side                      none
% 2.72/0.97  --res_ordering                          kbo
% 2.72/0.97  --res_to_prop_solver                    active
% 2.72/0.97  --res_prop_simpl_new                    false
% 2.72/0.97  --res_prop_simpl_given                  true
% 2.72/0.97  --res_passive_queue_type                priority_queues
% 2.72/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.97  --res_passive_queues_freq               [15;5]
% 2.72/0.97  --res_forward_subs                      full
% 2.72/0.97  --res_backward_subs                     full
% 2.72/0.97  --res_forward_subs_resolution           true
% 2.72/0.97  --res_backward_subs_resolution          true
% 2.72/0.97  --res_orphan_elimination                true
% 2.72/0.97  --res_time_limit                        2.
% 2.72/0.97  --res_out_proof                         true
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Options
% 2.72/0.97  
% 2.72/0.97  --superposition_flag                    true
% 2.72/0.97  --sup_passive_queue_type                priority_queues
% 2.72/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.97  --demod_completeness_check              fast
% 2.72/0.97  --demod_use_ground                      true
% 2.72/0.97  --sup_to_prop_solver                    passive
% 2.72/0.97  --sup_prop_simpl_new                    true
% 2.72/0.97  --sup_prop_simpl_given                  true
% 2.72/0.97  --sup_fun_splitting                     false
% 2.72/0.97  --sup_smt_interval                      50000
% 2.72/0.97  
% 2.72/0.97  ------ Superposition Simplification Setup
% 2.72/0.97  
% 2.72/0.97  --sup_indices_passive                   []
% 2.72/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_full_bw                           [BwDemod]
% 2.72/0.97  --sup_immed_triv                        [TrivRules]
% 2.72/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_immed_bw_main                     []
% 2.72/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.97  
% 2.72/0.97  ------ Combination Options
% 2.72/0.97  
% 2.72/0.97  --comb_res_mult                         3
% 2.72/0.97  --comb_sup_mult                         2
% 2.72/0.97  --comb_inst_mult                        10
% 2.72/0.97  
% 2.72/0.97  ------ Debug Options
% 2.72/0.97  
% 2.72/0.97  --dbg_backtrace                         false
% 2.72/0.97  --dbg_dump_prop_clauses                 false
% 2.72/0.97  --dbg_dump_prop_clauses_file            -
% 2.72/0.97  --dbg_out_stat                          false
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  ------ Proving...
% 2.72/0.97  
% 2.72/0.97  
% 2.72/0.97  % SZS status Theorem for theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.97  
% 2.72/0.97  fof(f5,axiom,(
% 2.72/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f44,plain,(
% 2.72/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f5])).
% 2.72/0.97  
% 2.72/0.97  fof(f2,axiom,(
% 2.72/0.97    v1_xboole_0(k1_xboole_0)),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f38,plain,(
% 2.72/0.97    v1_xboole_0(k1_xboole_0)),
% 2.72/0.97    inference(cnf_transformation,[],[f2])).
% 2.72/0.97  
% 2.72/0.97  fof(f7,axiom,(
% 2.72/0.97    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f16,plain,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f7])).
% 2.72/0.97  
% 2.72/0.97  fof(f47,plain,(
% 2.72/0.97    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f16])).
% 2.72/0.97  
% 2.72/0.97  fof(f11,axiom,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f20,plain,(
% 2.72/0.97    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f11])).
% 2.72/0.97  
% 2.72/0.97  fof(f56,plain,(
% 2.72/0.97    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f20])).
% 2.72/0.97  
% 2.72/0.97  fof(f10,axiom,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f18,plain,(
% 2.72/0.97    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f10])).
% 2.72/0.97  
% 2.72/0.97  fof(f19,plain,(
% 2.72/0.97    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(flattening,[],[f18])).
% 2.72/0.97  
% 2.72/0.97  fof(f54,plain,(
% 2.72/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f19])).
% 2.72/0.97  
% 2.72/0.97  fof(f9,axiom,(
% 2.72/0.97    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f17,plain,(
% 2.72/0.97    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.72/0.97    inference(ennf_transformation,[],[f9])).
% 2.72/0.97  
% 2.72/0.97  fof(f52,plain,(
% 2.72/0.97    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f17])).
% 2.72/0.97  
% 2.72/0.97  fof(f1,axiom,(
% 2.72/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f22,plain,(
% 2.72/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.97    inference(nnf_transformation,[],[f1])).
% 2.72/0.97  
% 2.72/0.97  fof(f23,plain,(
% 2.72/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.97    inference(rectify,[],[f22])).
% 2.72/0.97  
% 2.72/0.97  fof(f24,plain,(
% 2.72/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f25,plain,(
% 2.72/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.72/0.97  
% 2.72/0.97  fof(f37,plain,(
% 2.72/0.97    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f8,axiom,(
% 2.72/0.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f30,plain,(
% 2.72/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.72/0.97    inference(nnf_transformation,[],[f8])).
% 2.72/0.97  
% 2.72/0.97  fof(f31,plain,(
% 2.72/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.72/0.97    inference(rectify,[],[f30])).
% 2.72/0.97  
% 2.72/0.97  fof(f34,plain,(
% 2.72/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f33,plain,(
% 2.72/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0))) )),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f32,plain,(
% 2.72/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f35,plain,(
% 2.72/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.72/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 2.72/0.97  
% 2.72/0.97  fof(f48,plain,(
% 2.72/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.72/0.97    inference(cnf_transformation,[],[f35])).
% 2.72/0.97  
% 2.72/0.97  fof(f59,plain,(
% 2.72/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.72/0.97    inference(equality_resolution,[],[f48])).
% 2.72/0.97  
% 2.72/0.97  fof(f4,axiom,(
% 2.72/0.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f28,plain,(
% 2.72/0.97    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.72/0.97    inference(nnf_transformation,[],[f4])).
% 2.72/0.97  
% 2.72/0.97  fof(f43,plain,(
% 2.72/0.97    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f28])).
% 2.72/0.97  
% 2.72/0.97  fof(f6,axiom,(
% 2.72/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f29,plain,(
% 2.72/0.97    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.72/0.97    inference(nnf_transformation,[],[f6])).
% 2.72/0.97  
% 2.72/0.97  fof(f46,plain,(
% 2.72/0.97    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.72/0.97    inference(cnf_transformation,[],[f29])).
% 2.72/0.97  
% 2.72/0.97  fof(f3,axiom,(
% 2.72/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f14,plain,(
% 2.72/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.72/0.97    inference(rectify,[],[f3])).
% 2.72/0.97  
% 2.72/0.97  fof(f15,plain,(
% 2.72/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.72/0.97    inference(ennf_transformation,[],[f14])).
% 2.72/0.97  
% 2.72/0.97  fof(f26,plain,(
% 2.72/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.72/0.97    introduced(choice_axiom,[])).
% 2.72/0.97  
% 2.72/0.97  fof(f27,plain,(
% 2.72/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.72/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f26])).
% 2.72/0.97  
% 2.72/0.97  fof(f41,plain,(
% 2.72/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f27])).
% 2.72/0.97  
% 2.72/0.97  fof(f36,plain,(
% 2.72/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f25])).
% 2.72/0.97  
% 2.72/0.97  fof(f39,plain,(
% 2.72/0.97    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f27])).
% 2.72/0.97  
% 2.72/0.97  fof(f45,plain,(
% 2.72/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f29])).
% 2.72/0.97  
% 2.72/0.97  fof(f42,plain,(
% 2.72/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f28])).
% 2.72/0.97  
% 2.72/0.97  fof(f50,plain,(
% 2.72/0.97    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f35])).
% 2.72/0.97  
% 2.72/0.97  fof(f40,plain,(
% 2.72/0.97    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.72/0.97    inference(cnf_transformation,[],[f27])).
% 2.72/0.97  
% 2.72/0.97  fof(f12,conjecture,(
% 2.72/0.97    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.72/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.97  
% 2.72/0.97  fof(f13,negated_conjecture,(
% 2.72/0.97    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 2.72/0.97    inference(negated_conjecture,[],[f12])).
% 2.72/0.97  
% 2.72/0.97  fof(f21,plain,(
% 2.72/0.97    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.72/0.97    inference(ennf_transformation,[],[f13])).
% 2.72/0.97  
% 2.72/0.97  fof(f57,plain,(
% 2.72/0.97    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 2.72/0.97    inference(cnf_transformation,[],[f21])).
% 2.72/0.97  
% 2.72/0.97  cnf(c_8,plain,
% 2.72/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_949,plain,
% 2.72/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2,plain,
% 2.72/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_955,plain,
% 2.72/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_11,plain,
% 2.72/0.97      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_946,plain,
% 2.72/0.97      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1113,plain,
% 2.72/0.97      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_955,c_946]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_19,plain,
% 2.72/0.97      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_938,plain,
% 2.72/0.97      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 2.72/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1237,plain,
% 2.72/0.97      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_1113,c_938]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_17,plain,
% 2.72/0.97      ( ~ r1_tarski(X0,X1)
% 2.72/0.97      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.72/0.97      | ~ v1_relat_1(X0)
% 2.72/0.97      | ~ v1_relat_1(X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_940,plain,
% 2.72/0.97      ( r1_tarski(X0,X1) != iProver_top
% 2.72/0.97      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.72/0.97      | v1_relat_1(X0) != iProver_top
% 2.72/0.97      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2435,plain,
% 2.72/0.97      ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
% 2.72/0.97      | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 2.72/0.97      | v1_relat_1(X0) != iProver_top
% 2.72/0.97      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_1237,c_940]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_16,plain,
% 2.72/0.97      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.72/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_34,plain,
% 2.72/0.97      ( v1_relat_1(X0) != iProver_top
% 2.72/0.97      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_36,plain,
% 2.72/0.97      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 2.72/0.97      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_34]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_49,plain,
% 2.72/0.97      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_51,plain,
% 2.72/0.97      ( v1_relat_1(k1_xboole_0) = iProver_top
% 2.72/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.72/0.97      inference(instantiation,[status(thm)],[c_49]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_72,plain,
% 2.72/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_10806,plain,
% 2.72/0.97      ( v1_relat_1(X0) != iProver_top
% 2.72/0.97      | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 2.72/0.97      | r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_2435,c_36,c_51,c_72]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_10807,plain,
% 2.72/0.97      ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
% 2.72/0.97      | r1_tarski(k2_relat_1(X0),k1_relat_1(k1_xboole_0)) = iProver_top
% 2.72/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.97      inference(renaming,[status(thm)],[c_10806]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_0,plain,
% 2.72/0.97      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_957,plain,
% 2.72/0.97      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.72/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_15,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.97      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_942,plain,
% 2.72/0.97      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.72/0.97      | r2_hidden(k4_tarski(X0,sK4(X1,X0)),X1) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_6,plain,
% 2.72/0.97      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.72/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_951,plain,
% 2.72/0.97      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.72/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1440,plain,
% 2.72/0.97      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_949,c_951]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_9,plain,
% 2.72/0.97      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.72/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_948,plain,
% 2.72/0.97      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1444,plain,
% 2.72/0.97      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_1440,c_948]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3,plain,
% 2.72/0.97      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_954,plain,
% 2.72/0.97      ( r1_xboole_0(X0,X1) != iProver_top
% 2.72/0.97      | r2_hidden(X2,X0) != iProver_top
% 2.72/0.97      | r2_hidden(X2,X1) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_2522,plain,
% 2.72/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.72/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_1444,c_954]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.72/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_328,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.72/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_329,plain,
% 2.72/0.97      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.72/0.97      inference(unflattening,[status(thm)],[c_328]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_330,plain,
% 2.72/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3290,plain,
% 2.72/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.72/0.97      inference(global_propositional_subsumption,
% 2.72/0.97                [status(thm)],
% 2.72/0.97                [c_2522,c_330]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3299,plain,
% 2.72/0.97      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_942,c_3290]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_3390,plain,
% 2.72/0.97      ( v1_xboole_0(k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.72/0.97      inference(superposition,[status(thm)],[c_957,c_3299]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_5,plain,
% 2.72/0.97      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.72/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_952,plain,
% 2.72/0.97      ( r1_xboole_0(X0,X1) = iProver_top
% 2.72/0.97      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_956,plain,
% 2.72/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.72/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.72/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.72/0.97  
% 2.72/0.97  cnf(c_1733,plain,
% 2.72/0.97      ( r1_xboole_0(X0,X1) = iProver_top
% 2.72/0.97      | v1_xboole_0(X0) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_952,c_956]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_10,plain,
% 2.72/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.72/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_947,plain,
% 2.72/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1907,plain,
% 2.72/0.98      ( k4_xboole_0(X0,X1) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1733,c_947]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3417,plain,
% 2.72/0.98      ( k4_xboole_0(k1_relat_1(k1_xboole_0),X0) = k1_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3390,c_1907]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_7,plain,
% 2.72/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.72/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_950,plain,
% 2.72/0.98      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.72/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3695,plain,
% 2.72/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.72/0.98      | r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3417,c_950]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_13,plain,
% 2.72/0.98      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 2.72/0.98      | r2_hidden(sK2(X0,X1),X1)
% 2.72/0.98      | k1_relat_1(X0) = X1 ),
% 2.72/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_44,plain,
% 2.72/0.98      ( r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 2.72/0.98      | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1477,plain,
% 2.72/0.98      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 2.72/0.98      | ~ v1_xboole_0(X0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1484,plain,
% 2.72/0.98      ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 2.72/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1477]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1750,plain,
% 2.72/0.98      ( ~ r2_hidden(sK2(X0,X1),X1) | ~ v1_xboole_0(X1) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1757,plain,
% 2.72/0.98      ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1750]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6828,plain,
% 2.72/0.98      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_3695,c_44,c_2,c_1484,c_1757]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6835,plain,
% 2.72/0.98      ( k4_xboole_0(k1_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_6828,c_951]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6838,plain,
% 2.72/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.72/0.98      inference(demodulation,[status(thm)],[c_6835,c_3417]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_10812,plain,
% 2.72/0.98      ( r1_tarski(X0,k4_relat_1(k1_xboole_0)) != iProver_top
% 2.72/0.98      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top
% 2.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.98      inference(light_normalisation,[status(thm)],[c_10807,c_6838]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_10819,plain,
% 2.72/0.98      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 2.72/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_949,c_10812]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3006,plain,
% 2.72/0.98      ( ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),X0)
% 2.72/0.98      | ~ v1_xboole_0(X0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3013,plain,
% 2.72/0.98      ( ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_3006]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1392,plain,
% 2.72/0.98      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1393,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k1_xboole_0
% 2.72/0.98      | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1395,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 2.72/0.98      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_4,plain,
% 2.72/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.72/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1293,plain,
% 2.72/0.98      ( r1_xboole_0(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),X0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1300,plain,
% 2.72/0.98      ( r1_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | r2_hidden(sK1(k2_relat_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1293]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_415,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1250,plain,
% 2.72/0.98      ( k1_relat_1(X0) != X1
% 2.72/0.98      | k1_xboole_0 != X1
% 2.72/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1251,plain,
% 2.72/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.72/0.98      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1250]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1231,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) != X1
% 2.72/0.98      | k1_xboole_0 != X1
% 2.72/0.98      | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),X0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1232,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 2.72/0.98      | k1_xboole_0 = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1231]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1106,plain,
% 2.72/0.98      ( k2_relat_1(k1_xboole_0) != X0
% 2.72/0.98      | k1_xboole_0 != X0
% 2.72/0.98      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1200,plain,
% 2.72/0.98      ( k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1106]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1201,plain,
% 2.72/0.98      ( k2_relat_1(k1_xboole_0) != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 != k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1200]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1136,plain,
% 2.72/0.98      ( ~ r1_xboole_0(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | k4_xboole_0(k2_relat_1(k1_xboole_0),X0) = k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1139,plain,
% 2.72/0.98      ( ~ r1_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1136]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1121,plain,
% 2.72/0.98      ( X0 != X1
% 2.72/0.98      | k2_relat_1(k1_xboole_0) != X1
% 2.72/0.98      | k2_relat_1(k1_xboole_0) = X0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1126,plain,
% 2.72/0.98      ( X0 != k2_relat_1(k1_xboole_0)
% 2.72/0.98      | k2_relat_1(k1_xboole_0) = X0
% 2.72/0.98      | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1121]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1135,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),X0) != k2_relat_1(k1_xboole_0)
% 2.72/0.98      | k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(k1_xboole_0),X0)
% 2.72/0.98      | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1126]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1137,plain,
% 2.72/0.98      ( k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0) != k2_relat_1(k1_xboole_0)
% 2.72/0.98      | k2_relat_1(k1_xboole_0) = k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)
% 2.72/0.98      | k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1135]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_414,plain,( X0 = X0 ),theory(equality) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_431,plain,
% 2.72/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_414]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_422,plain,
% 2.72/0.98      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 2.72/0.98      theory(equality) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_429,plain,
% 2.72/0.98      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_422]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_21,negated_conjecture,
% 2.72/0.98      ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 2.72/0.98      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(contradiction,plain,
% 2.72/0.98      ( $false ),
% 2.72/0.98      inference(minisat,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_10819,c_3013,c_1757,c_1484,c_1395,c_1300,c_1251,
% 2.72/0.98                 c_1232,c_1201,c_1139,c_1137,c_431,c_429,c_72,c_2,c_51,
% 2.72/0.98                 c_44,c_21]) ).
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.98  
% 2.72/0.98  ------                               Statistics
% 2.72/0.98  
% 2.72/0.98  ------ General
% 2.72/0.98  
% 2.72/0.98  abstr_ref_over_cycles:                  0
% 2.72/0.98  abstr_ref_under_cycles:                 0
% 2.72/0.98  gc_basic_clause_elim:                   0
% 2.72/0.98  forced_gc_time:                         0
% 2.72/0.98  parsing_time:                           0.009
% 2.72/0.98  unif_index_cands_time:                  0.
% 2.72/0.98  unif_index_add_time:                    0.
% 2.72/0.98  orderings_time:                         0.
% 2.72/0.98  out_proof_time:                         0.008
% 2.72/0.98  total_time:                             0.277
% 2.72/0.98  num_of_symbols:                         47
% 2.72/0.98  num_of_terms:                           6661
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing
% 2.72/0.98  
% 2.72/0.98  num_of_splits:                          0
% 2.72/0.98  num_of_split_atoms:                     0
% 2.72/0.98  num_of_reused_defs:                     0
% 2.72/0.98  num_eq_ax_congr_red:                    28
% 2.72/0.98  num_of_sem_filtered_clauses:            1
% 2.72/0.98  num_of_subtypes:                        0
% 2.72/0.98  monotx_restored_types:                  0
% 2.72/0.98  sat_num_of_epr_types:                   0
% 2.72/0.98  sat_num_of_non_cyclic_types:            0
% 2.72/0.98  sat_guarded_non_collapsed_types:        0
% 2.72/0.98  num_pure_diseq_elim:                    0
% 2.72/0.98  simp_replaced_by:                       0
% 2.72/0.98  res_preprocessed:                       85
% 2.72/0.98  prep_upred:                             0
% 2.72/0.98  prep_unflattend:                        3
% 2.72/0.98  smt_new_axioms:                         0
% 2.72/0.98  pred_elim_cands:                        5
% 2.72/0.98  pred_elim:                              0
% 2.72/0.98  pred_elim_cl:                           0
% 2.72/0.98  pred_elim_cycles:                       2
% 2.72/0.98  merged_defs:                            12
% 2.72/0.98  merged_defs_ncl:                        0
% 2.72/0.98  bin_hyper_res:                          12
% 2.72/0.98  prep_cycles:                            3
% 2.72/0.98  pred_elim_time:                         0.001
% 2.72/0.98  splitting_time:                         0.
% 2.72/0.98  sem_filter_time:                        0.
% 2.72/0.98  monotx_time:                            0.
% 2.72/0.98  subtype_inf_time:                       0.
% 2.72/0.98  
% 2.72/0.98  ------ Problem properties
% 2.72/0.98  
% 2.72/0.98  clauses:                                22
% 2.72/0.98  conjectures:                            1
% 2.72/0.98  epr:                                    5
% 2.72/0.98  horn:                                   18
% 2.72/0.98  ground:                                 2
% 2.72/0.98  unary:                                  2
% 2.72/0.98  binary:                                 15
% 2.72/0.98  lits:                                   49
% 2.72/0.98  lits_eq:                                10
% 2.72/0.98  fd_pure:                                0
% 2.72/0.98  fd_pseudo:                              0
% 2.72/0.98  fd_cond:                                0
% 2.72/0.98  fd_pseudo_cond:                         2
% 2.72/0.98  ac_symbols:                             0
% 2.72/0.98  
% 2.72/0.98  ------ Propositional Solver
% 2.72/0.98  
% 2.72/0.98  prop_solver_calls:                      27
% 2.72/0.98  prop_fast_solver_calls:                 714
% 2.72/0.98  smt_solver_calls:                       0
% 2.72/0.98  smt_fast_solver_calls:                  0
% 2.72/0.98  prop_num_of_clauses:                    2877
% 2.72/0.98  prop_preprocess_simplified:             8562
% 2.72/0.98  prop_fo_subsumed:                       18
% 2.72/0.98  prop_solver_time:                       0.
% 2.72/0.98  smt_solver_time:                        0.
% 2.72/0.98  smt_fast_solver_time:                   0.
% 2.72/0.98  prop_fast_solver_time:                  0.
% 2.72/0.98  prop_unsat_core_time:                   0.
% 2.72/0.98  
% 2.72/0.98  ------ QBF
% 2.72/0.98  
% 2.72/0.98  qbf_q_res:                              0
% 2.72/0.98  qbf_num_tautologies:                    0
% 2.72/0.98  qbf_prep_cycles:                        0
% 2.72/0.98  
% 2.72/0.98  ------ BMC1
% 2.72/0.98  
% 2.72/0.98  bmc1_current_bound:                     -1
% 2.72/0.98  bmc1_last_solved_bound:                 -1
% 2.72/0.98  bmc1_unsat_core_size:                   -1
% 2.72/0.98  bmc1_unsat_core_parents_size:           -1
% 2.72/0.98  bmc1_merge_next_fun:                    0
% 2.72/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.98  
% 2.72/0.98  ------ Instantiation
% 2.72/0.98  
% 2.72/0.98  inst_num_of_clauses:                    1157
% 2.72/0.98  inst_num_in_passive:                    603
% 2.72/0.98  inst_num_in_active:                     472
% 2.72/0.98  inst_num_in_unprocessed:                82
% 2.72/0.98  inst_num_of_loops:                      630
% 2.72/0.98  inst_num_of_learning_restarts:          0
% 2.72/0.98  inst_num_moves_active_passive:          150
% 2.72/0.98  inst_lit_activity:                      0
% 2.72/0.98  inst_lit_activity_moves:                0
% 2.72/0.98  inst_num_tautologies:                   0
% 2.72/0.98  inst_num_prop_implied:                  0
% 2.72/0.98  inst_num_existing_simplified:           0
% 2.72/0.98  inst_num_eq_res_simplified:             0
% 2.72/0.98  inst_num_child_elim:                    0
% 2.72/0.98  inst_num_of_dismatching_blockings:      1280
% 2.72/0.98  inst_num_of_non_proper_insts:           1802
% 2.72/0.98  inst_num_of_duplicates:                 0
% 2.72/0.98  inst_inst_num_from_inst_to_res:         0
% 2.72/0.98  inst_dismatching_checking_time:         0.
% 2.72/0.98  
% 2.72/0.98  ------ Resolution
% 2.72/0.98  
% 2.72/0.98  res_num_of_clauses:                     0
% 2.72/0.98  res_num_in_passive:                     0
% 2.72/0.98  res_num_in_active:                      0
% 2.72/0.98  res_num_of_loops:                       88
% 2.72/0.98  res_forward_subset_subsumed:            107
% 2.72/0.98  res_backward_subset_subsumed:           2
% 2.72/0.98  res_forward_subsumed:                   0
% 2.72/0.98  res_backward_subsumed:                  0
% 2.72/0.98  res_forward_subsumption_resolution:     0
% 2.72/0.98  res_backward_subsumption_resolution:    0
% 2.72/0.98  res_clause_to_clause_subsumption:       740
% 2.72/0.98  res_orphan_elimination:                 0
% 2.72/0.98  res_tautology_del:                      257
% 2.72/0.98  res_num_eq_res_simplified:              0
% 2.72/0.98  res_num_sel_changes:                    0
% 2.72/0.98  res_moves_from_active_to_pass:          0
% 2.72/0.98  
% 2.72/0.98  ------ Superposition
% 2.72/0.98  
% 2.72/0.98  sup_time_total:                         0.
% 2.72/0.98  sup_time_generating:                    0.
% 2.72/0.98  sup_time_sim_full:                      0.
% 2.72/0.98  sup_time_sim_immed:                     0.
% 2.72/0.98  
% 2.72/0.98  sup_num_of_clauses:                     197
% 2.72/0.98  sup_num_in_active:                      76
% 2.72/0.98  sup_num_in_passive:                     121
% 2.72/0.98  sup_num_of_loops:                       125
% 2.72/0.98  sup_fw_superposition:                   180
% 2.72/0.98  sup_bw_superposition:                   231
% 2.72/0.98  sup_immediate_simplified:               87
% 2.72/0.98  sup_given_eliminated:                   0
% 2.72/0.98  comparisons_done:                       0
% 2.72/0.98  comparisons_avoided:                    0
% 2.72/0.98  
% 2.72/0.98  ------ Simplifications
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  sim_fw_subset_subsumed:                 40
% 2.72/0.98  sim_bw_subset_subsumed:                 6
% 2.72/0.98  sim_fw_subsumed:                        12
% 2.72/0.98  sim_bw_subsumed:                        0
% 2.72/0.98  sim_fw_subsumption_res:                 0
% 2.72/0.98  sim_bw_subsumption_res:                 0
% 2.72/0.98  sim_tautology_del:                      6
% 2.72/0.98  sim_eq_tautology_del:                   19
% 2.72/0.98  sim_eq_res_simp:                        1
% 2.72/0.98  sim_fw_demodulated:                     2
% 2.72/0.98  sim_bw_demodulated:                     50
% 2.72/0.98  sim_light_normalised:                   62
% 2.72/0.98  sim_joinable_taut:                      0
% 2.72/0.98  sim_joinable_simp:                      0
% 2.72/0.98  sim_ac_normalised:                      0
% 2.72/0.98  sim_smt_subsumption:                    0
% 2.72/0.98  
%------------------------------------------------------------------------------
