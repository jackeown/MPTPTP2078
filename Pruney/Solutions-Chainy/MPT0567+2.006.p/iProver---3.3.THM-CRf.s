%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:58 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 760 expanded)
%              Number of clauses        :   68 ( 276 expanded)
%              Number of leaves         :   13 ( 170 expanded)
%              Depth                    :   17
%              Number of atoms          :  345 (2077 expanded)
%              Number of equality atoms :  157 (1067 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f24])).

fof(f40,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f41,plain,(
    k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f35,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_268,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_269,plain,
    ( r2_hidden(sK2(sK4,X0,X1),X0)
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_851,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top
    | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_853,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_856,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1278,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_853,c_856])).

cnf(c_1528,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_1278])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1771,plain,
    ( k10_relat_1(sK4,X0) != k1_xboole_0
    | k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_13])).

cnf(c_1772,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(equality_factoring,[status(thm)],[c_1528])).

cnf(c_1790,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1772,c_1528])).

cnf(c_1794,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_2987,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_1794])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_855,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4691,plain,
    ( X0 = X1
    | r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_855])).

cnf(c_36,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17506,plain,
    ( r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4691,c_36])).

cnf(c_17507,plain,
    ( X0 = X1
    | r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_17506])).

cnf(c_17521,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2987,c_17507])).

cnf(c_539,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_969,plain,
    ( k10_relat_1(sK4,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1729,plain,
    ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_1528,c_13])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_34,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) != k1_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_35,plain,
    ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2586,plain,
    ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_3008,plain,
    ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1729,c_34,c_35,c_2586])).

cnf(c_17522,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = X0
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3008,c_17507])).

cnf(c_19554,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17521,c_13,c_969,c_17522])).

cnf(c_19555,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19554])).

cnf(c_19563,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = X0
    | r2_hidden(sK1(sK4,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_19555])).

cnf(c_19588,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19563])).

cnf(c_19562,plain,
    ( k10_relat_1(sK4,X0) = k1_xboole_0
    | r2_hidden(sK2(sK4,X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_19555])).

cnf(c_19585,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19562])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_253,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_254,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(sK4,X0,X1),sK2(sK4,X0,X1)),sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_852,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK1(sK4,X0,X1),sK2(sK4,X0,X1)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_302,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK4,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_849,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_1150,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(sK2(sK4,X0,X1),X2) != iProver_top
    | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_849])).

cnf(c_19561,plain,
    ( k10_relat_1(sK4,X0) = k1_xboole_0
    | r2_hidden(sK2(sK4,X0,k1_xboole_0),X1) != iProver_top
    | r2_hidden(sK1(sK4,X0,k1_xboole_0),k10_relat_1(sK4,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_19555])).

cnf(c_19582,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK2(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19561])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(sK3(sK4,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_847,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK3(sK4,X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK3(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK3(X1,X2,X0)),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X0,sK3(sK4,X1,X0)),sK4) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_848,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(sK4,X1,X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK1(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK1(X2,X1,X3),X0),X2)
    | k10_relat_1(X2,X1) = X3
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK4,X1,X2),X2)
    | ~ r2_hidden(k4_tarski(sK1(sK4,X1,X2),X0),sK4)
    | k10_relat_1(sK4,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_850,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK4,X0,X1),X2),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1061,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(sK3(sK4,X2,sK1(sK4,X0,X1)),X0) != iProver_top
    | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
    | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_850])).

cnf(c_1349,plain,
    ( k10_relat_1(sK4,X0) = X1
    | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
    | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_1061])).

cnf(c_1351,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) != iProver_top
    | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_970,plain,
    ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19588,c_19585,c_19582,c_1351,c_970,c_35,c_34,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.63/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.99  
% 3.63/0.99  ------  iProver source info
% 3.63/0.99  
% 3.63/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.99  git: non_committed_changes: false
% 3.63/0.99  git: last_make_outside_of_git: false
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options
% 3.63/0.99  
% 3.63/0.99  --out_options                           all
% 3.63/0.99  --tptp_safe_out                         true
% 3.63/0.99  --problem_path                          ""
% 3.63/0.99  --include_path                          ""
% 3.63/0.99  --clausifier                            res/vclausify_rel
% 3.63/0.99  --clausifier_options                    --mode clausify
% 3.63/0.99  --stdin                                 false
% 3.63/0.99  --stats_out                             all
% 3.63/0.99  
% 3.63/0.99  ------ General Options
% 3.63/0.99  
% 3.63/0.99  --fof                                   false
% 3.63/0.99  --time_out_real                         305.
% 3.63/0.99  --time_out_virtual                      -1.
% 3.63/0.99  --symbol_type_check                     false
% 3.63/0.99  --clausify_out                          false
% 3.63/0.99  --sig_cnt_out                           false
% 3.63/0.99  --trig_cnt_out                          false
% 3.63/0.99  --trig_cnt_out_tolerance                1.
% 3.63/0.99  --trig_cnt_out_sk_spl                   false
% 3.63/0.99  --abstr_cl_out                          false
% 3.63/0.99  
% 3.63/0.99  ------ Global Options
% 3.63/0.99  
% 3.63/0.99  --schedule                              default
% 3.63/0.99  --add_important_lit                     false
% 3.63/0.99  --prop_solver_per_cl                    1000
% 3.63/0.99  --min_unsat_core                        false
% 3.63/0.99  --soft_assumptions                      false
% 3.63/0.99  --soft_lemma_size                       3
% 3.63/0.99  --prop_impl_unit_size                   0
% 3.63/0.99  --prop_impl_unit                        []
% 3.63/0.99  --share_sel_clauses                     true
% 3.63/0.99  --reset_solvers                         false
% 3.63/0.99  --bc_imp_inh                            [conj_cone]
% 3.63/0.99  --conj_cone_tolerance                   3.
% 3.63/0.99  --extra_neg_conj                        none
% 3.63/0.99  --large_theory_mode                     true
% 3.63/0.99  --prolific_symb_bound                   200
% 3.63/0.99  --lt_threshold                          2000
% 3.63/0.99  --clause_weak_htbl                      true
% 3.63/0.99  --gc_record_bc_elim                     false
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing Options
% 3.63/0.99  
% 3.63/0.99  --preprocessing_flag                    true
% 3.63/0.99  --time_out_prep_mult                    0.1
% 3.63/0.99  --splitting_mode                        input
% 3.63/0.99  --splitting_grd                         true
% 3.63/0.99  --splitting_cvd                         false
% 3.63/0.99  --splitting_cvd_svl                     false
% 3.63/0.99  --splitting_nvd                         32
% 3.63/0.99  --sub_typing                            true
% 3.63/0.99  --prep_gs_sim                           true
% 3.63/0.99  --prep_unflatten                        true
% 3.63/0.99  --prep_res_sim                          true
% 3.63/0.99  --prep_upred                            true
% 3.63/0.99  --prep_sem_filter                       exhaustive
% 3.63/0.99  --prep_sem_filter_out                   false
% 3.63/0.99  --pred_elim                             true
% 3.63/0.99  --res_sim_input                         true
% 3.63/0.99  --eq_ax_congr_red                       true
% 3.63/0.99  --pure_diseq_elim                       true
% 3.63/0.99  --brand_transform                       false
% 3.63/0.99  --non_eq_to_eq                          false
% 3.63/0.99  --prep_def_merge                        true
% 3.63/0.99  --prep_def_merge_prop_impl              false
% 3.63/0.99  --prep_def_merge_mbd                    true
% 3.63/0.99  --prep_def_merge_tr_red                 false
% 3.63/0.99  --prep_def_merge_tr_cl                  false
% 3.63/0.99  --smt_preprocessing                     true
% 3.63/0.99  --smt_ac_axioms                         fast
% 3.63/0.99  --preprocessed_out                      false
% 3.63/0.99  --preprocessed_stats                    false
% 3.63/0.99  
% 3.63/0.99  ------ Abstraction refinement Options
% 3.63/0.99  
% 3.63/0.99  --abstr_ref                             []
% 3.63/0.99  --abstr_ref_prep                        false
% 3.63/0.99  --abstr_ref_until_sat                   false
% 3.63/0.99  --abstr_ref_sig_restrict                funpre
% 3.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.99  --abstr_ref_under                       []
% 3.63/0.99  
% 3.63/0.99  ------ SAT Options
% 3.63/0.99  
% 3.63/0.99  --sat_mode                              false
% 3.63/0.99  --sat_fm_restart_options                ""
% 3.63/0.99  --sat_gr_def                            false
% 3.63/0.99  --sat_epr_types                         true
% 3.63/0.99  --sat_non_cyclic_types                  false
% 3.63/0.99  --sat_finite_models                     false
% 3.63/0.99  --sat_fm_lemmas                         false
% 3.63/0.99  --sat_fm_prep                           false
% 3.63/0.99  --sat_fm_uc_incr                        true
% 3.63/0.99  --sat_out_model                         small
% 3.63/0.99  --sat_out_clauses                       false
% 3.63/0.99  
% 3.63/0.99  ------ QBF Options
% 3.63/0.99  
% 3.63/0.99  --qbf_mode                              false
% 3.63/0.99  --qbf_elim_univ                         false
% 3.63/0.99  --qbf_dom_inst                          none
% 3.63/0.99  --qbf_dom_pre_inst                      false
% 3.63/0.99  --qbf_sk_in                             false
% 3.63/0.99  --qbf_pred_elim                         true
% 3.63/0.99  --qbf_split                             512
% 3.63/0.99  
% 3.63/0.99  ------ BMC1 Options
% 3.63/0.99  
% 3.63/0.99  --bmc1_incremental                      false
% 3.63/0.99  --bmc1_axioms                           reachable_all
% 3.63/0.99  --bmc1_min_bound                        0
% 3.63/0.99  --bmc1_max_bound                        -1
% 3.63/0.99  --bmc1_max_bound_default                -1
% 3.63/0.99  --bmc1_symbol_reachability              true
% 3.63/0.99  --bmc1_property_lemmas                  false
% 3.63/0.99  --bmc1_k_induction                      false
% 3.63/0.99  --bmc1_non_equiv_states                 false
% 3.63/0.99  --bmc1_deadlock                         false
% 3.63/0.99  --bmc1_ucm                              false
% 3.63/0.99  --bmc1_add_unsat_core                   none
% 3.63/0.99  --bmc1_unsat_core_children              false
% 3.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.99  --bmc1_out_stat                         full
% 3.63/0.99  --bmc1_ground_init                      false
% 3.63/0.99  --bmc1_pre_inst_next_state              false
% 3.63/0.99  --bmc1_pre_inst_state                   false
% 3.63/0.99  --bmc1_pre_inst_reach_state             false
% 3.63/0.99  --bmc1_out_unsat_core                   false
% 3.63/0.99  --bmc1_aig_witness_out                  false
% 3.63/0.99  --bmc1_verbose                          false
% 3.63/0.99  --bmc1_dump_clauses_tptp                false
% 3.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.99  --bmc1_dump_file                        -
% 3.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.99  --bmc1_ucm_extend_mode                  1
% 3.63/0.99  --bmc1_ucm_init_mode                    2
% 3.63/0.99  --bmc1_ucm_cone_mode                    none
% 3.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.99  --bmc1_ucm_relax_model                  4
% 3.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.99  --bmc1_ucm_layered_model                none
% 3.63/0.99  --bmc1_ucm_max_lemma_size               10
% 3.63/0.99  
% 3.63/0.99  ------ AIG Options
% 3.63/0.99  
% 3.63/0.99  --aig_mode                              false
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation Options
% 3.63/0.99  
% 3.63/0.99  --instantiation_flag                    true
% 3.63/0.99  --inst_sos_flag                         false
% 3.63/0.99  --inst_sos_phase                        true
% 3.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel_side                     num_symb
% 3.63/0.99  --inst_solver_per_active                1400
% 3.63/0.99  --inst_solver_calls_frac                1.
% 3.63/0.99  --inst_passive_queue_type               priority_queues
% 3.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.99  --inst_passive_queues_freq              [25;2]
% 3.63/0.99  --inst_dismatching                      true
% 3.63/0.99  --inst_eager_unprocessed_to_passive     true
% 3.63/0.99  --inst_prop_sim_given                   true
% 3.63/0.99  --inst_prop_sim_new                     false
% 3.63/0.99  --inst_subs_new                         false
% 3.63/0.99  --inst_eq_res_simp                      false
% 3.63/0.99  --inst_subs_given                       false
% 3.63/0.99  --inst_orphan_elimination               true
% 3.63/0.99  --inst_learning_loop_flag               true
% 3.63/0.99  --inst_learning_start                   3000
% 3.63/0.99  --inst_learning_factor                  2
% 3.63/0.99  --inst_start_prop_sim_after_learn       3
% 3.63/0.99  --inst_sel_renew                        solver
% 3.63/0.99  --inst_lit_activity_flag                true
% 3.63/0.99  --inst_restr_to_given                   false
% 3.63/0.99  --inst_activity_threshold               500
% 3.63/0.99  --inst_out_proof                        true
% 3.63/0.99  
% 3.63/0.99  ------ Resolution Options
% 3.63/0.99  
% 3.63/0.99  --resolution_flag                       true
% 3.63/0.99  --res_lit_sel                           adaptive
% 3.63/0.99  --res_lit_sel_side                      none
% 3.63/0.99  --res_ordering                          kbo
% 3.63/0.99  --res_to_prop_solver                    active
% 3.63/0.99  --res_prop_simpl_new                    false
% 3.63/0.99  --res_prop_simpl_given                  true
% 3.63/0.99  --res_passive_queue_type                priority_queues
% 3.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.99  --res_passive_queues_freq               [15;5]
% 3.63/0.99  --res_forward_subs                      full
% 3.63/0.99  --res_backward_subs                     full
% 3.63/0.99  --res_forward_subs_resolution           true
% 3.63/0.99  --res_backward_subs_resolution          true
% 3.63/0.99  --res_orphan_elimination                true
% 3.63/0.99  --res_time_limit                        2.
% 3.63/0.99  --res_out_proof                         true
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Options
% 3.63/0.99  
% 3.63/0.99  --superposition_flag                    true
% 3.63/0.99  --sup_passive_queue_type                priority_queues
% 3.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.99  --demod_completeness_check              fast
% 3.63/0.99  --demod_use_ground                      true
% 3.63/0.99  --sup_to_prop_solver                    passive
% 3.63/0.99  --sup_prop_simpl_new                    true
% 3.63/0.99  --sup_prop_simpl_given                  true
% 3.63/0.99  --sup_fun_splitting                     false
% 3.63/0.99  --sup_smt_interval                      50000
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Simplification Setup
% 3.63/0.99  
% 3.63/0.99  --sup_indices_passive                   []
% 3.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_full_bw                           [BwDemod]
% 3.63/0.99  --sup_immed_triv                        [TrivRules]
% 3.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_immed_bw_main                     []
% 3.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  
% 3.63/0.99  ------ Combination Options
% 3.63/0.99  
% 3.63/0.99  --comb_res_mult                         3
% 3.63/0.99  --comb_sup_mult                         2
% 3.63/0.99  --comb_inst_mult                        10
% 3.63/0.99  
% 3.63/0.99  ------ Debug Options
% 3.63/0.99  
% 3.63/0.99  --dbg_backtrace                         false
% 3.63/0.99  --dbg_dump_prop_clauses                 false
% 3.63/0.99  --dbg_dump_prop_clauses_file            -
% 3.63/0.99  --dbg_out_stat                          false
% 3.63/0.99  ------ Parsing...
% 3.63/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.99  ------ Proving...
% 3.63/0.99  ------ Problem Properties 
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  clauses                                 14
% 3.63/0.99  conjectures                             1
% 3.63/0.99  EPR                                     0
% 3.63/0.99  Horn                                    9
% 3.63/0.99  unary                                   2
% 3.63/0.99  binary                                  8
% 3.63/0.99  lits                                    31
% 3.63/0.99  lits eq                                 10
% 3.63/0.99  fd_pure                                 0
% 3.63/0.99  fd_pseudo                               0
% 3.63/0.99  fd_cond                                 0
% 3.63/0.99  fd_pseudo_cond                          5
% 3.63/0.99  AC symbols                              0
% 3.63/0.99  
% 3.63/0.99  ------ Schedule dynamic 5 is on 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ 
% 3.63/0.99  Current options:
% 3.63/0.99  ------ 
% 3.63/0.99  
% 3.63/0.99  ------ Input Options
% 3.63/0.99  
% 3.63/0.99  --out_options                           all
% 3.63/0.99  --tptp_safe_out                         true
% 3.63/0.99  --problem_path                          ""
% 3.63/0.99  --include_path                          ""
% 3.63/0.99  --clausifier                            res/vclausify_rel
% 3.63/0.99  --clausifier_options                    --mode clausify
% 3.63/0.99  --stdin                                 false
% 3.63/0.99  --stats_out                             all
% 3.63/0.99  
% 3.63/0.99  ------ General Options
% 3.63/0.99  
% 3.63/0.99  --fof                                   false
% 3.63/0.99  --time_out_real                         305.
% 3.63/0.99  --time_out_virtual                      -1.
% 3.63/0.99  --symbol_type_check                     false
% 3.63/0.99  --clausify_out                          false
% 3.63/0.99  --sig_cnt_out                           false
% 3.63/0.99  --trig_cnt_out                          false
% 3.63/0.99  --trig_cnt_out_tolerance                1.
% 3.63/0.99  --trig_cnt_out_sk_spl                   false
% 3.63/0.99  --abstr_cl_out                          false
% 3.63/0.99  
% 3.63/0.99  ------ Global Options
% 3.63/0.99  
% 3.63/0.99  --schedule                              default
% 3.63/0.99  --add_important_lit                     false
% 3.63/0.99  --prop_solver_per_cl                    1000
% 3.63/0.99  --min_unsat_core                        false
% 3.63/0.99  --soft_assumptions                      false
% 3.63/0.99  --soft_lemma_size                       3
% 3.63/0.99  --prop_impl_unit_size                   0
% 3.63/0.99  --prop_impl_unit                        []
% 3.63/0.99  --share_sel_clauses                     true
% 3.63/0.99  --reset_solvers                         false
% 3.63/0.99  --bc_imp_inh                            [conj_cone]
% 3.63/0.99  --conj_cone_tolerance                   3.
% 3.63/0.99  --extra_neg_conj                        none
% 3.63/0.99  --large_theory_mode                     true
% 3.63/0.99  --prolific_symb_bound                   200
% 3.63/0.99  --lt_threshold                          2000
% 3.63/0.99  --clause_weak_htbl                      true
% 3.63/0.99  --gc_record_bc_elim                     false
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing Options
% 3.63/0.99  
% 3.63/0.99  --preprocessing_flag                    true
% 3.63/0.99  --time_out_prep_mult                    0.1
% 3.63/0.99  --splitting_mode                        input
% 3.63/0.99  --splitting_grd                         true
% 3.63/0.99  --splitting_cvd                         false
% 3.63/0.99  --splitting_cvd_svl                     false
% 3.63/0.99  --splitting_nvd                         32
% 3.63/0.99  --sub_typing                            true
% 3.63/0.99  --prep_gs_sim                           true
% 3.63/0.99  --prep_unflatten                        true
% 3.63/0.99  --prep_res_sim                          true
% 3.63/0.99  --prep_upred                            true
% 3.63/0.99  --prep_sem_filter                       exhaustive
% 3.63/0.99  --prep_sem_filter_out                   false
% 3.63/0.99  --pred_elim                             true
% 3.63/0.99  --res_sim_input                         true
% 3.63/0.99  --eq_ax_congr_red                       true
% 3.63/0.99  --pure_diseq_elim                       true
% 3.63/0.99  --brand_transform                       false
% 3.63/0.99  --non_eq_to_eq                          false
% 3.63/0.99  --prep_def_merge                        true
% 3.63/0.99  --prep_def_merge_prop_impl              false
% 3.63/0.99  --prep_def_merge_mbd                    true
% 3.63/0.99  --prep_def_merge_tr_red                 false
% 3.63/0.99  --prep_def_merge_tr_cl                  false
% 3.63/0.99  --smt_preprocessing                     true
% 3.63/0.99  --smt_ac_axioms                         fast
% 3.63/0.99  --preprocessed_out                      false
% 3.63/0.99  --preprocessed_stats                    false
% 3.63/0.99  
% 3.63/0.99  ------ Abstraction refinement Options
% 3.63/0.99  
% 3.63/0.99  --abstr_ref                             []
% 3.63/0.99  --abstr_ref_prep                        false
% 3.63/0.99  --abstr_ref_until_sat                   false
% 3.63/0.99  --abstr_ref_sig_restrict                funpre
% 3.63/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.99  --abstr_ref_under                       []
% 3.63/0.99  
% 3.63/0.99  ------ SAT Options
% 3.63/0.99  
% 3.63/0.99  --sat_mode                              false
% 3.63/0.99  --sat_fm_restart_options                ""
% 3.63/0.99  --sat_gr_def                            false
% 3.63/0.99  --sat_epr_types                         true
% 3.63/0.99  --sat_non_cyclic_types                  false
% 3.63/0.99  --sat_finite_models                     false
% 3.63/0.99  --sat_fm_lemmas                         false
% 3.63/0.99  --sat_fm_prep                           false
% 3.63/0.99  --sat_fm_uc_incr                        true
% 3.63/0.99  --sat_out_model                         small
% 3.63/0.99  --sat_out_clauses                       false
% 3.63/0.99  
% 3.63/0.99  ------ QBF Options
% 3.63/0.99  
% 3.63/0.99  --qbf_mode                              false
% 3.63/0.99  --qbf_elim_univ                         false
% 3.63/0.99  --qbf_dom_inst                          none
% 3.63/0.99  --qbf_dom_pre_inst                      false
% 3.63/0.99  --qbf_sk_in                             false
% 3.63/0.99  --qbf_pred_elim                         true
% 3.63/0.99  --qbf_split                             512
% 3.63/0.99  
% 3.63/0.99  ------ BMC1 Options
% 3.63/0.99  
% 3.63/0.99  --bmc1_incremental                      false
% 3.63/0.99  --bmc1_axioms                           reachable_all
% 3.63/0.99  --bmc1_min_bound                        0
% 3.63/0.99  --bmc1_max_bound                        -1
% 3.63/0.99  --bmc1_max_bound_default                -1
% 3.63/0.99  --bmc1_symbol_reachability              true
% 3.63/0.99  --bmc1_property_lemmas                  false
% 3.63/0.99  --bmc1_k_induction                      false
% 3.63/0.99  --bmc1_non_equiv_states                 false
% 3.63/0.99  --bmc1_deadlock                         false
% 3.63/0.99  --bmc1_ucm                              false
% 3.63/0.99  --bmc1_add_unsat_core                   none
% 3.63/0.99  --bmc1_unsat_core_children              false
% 3.63/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.99  --bmc1_out_stat                         full
% 3.63/0.99  --bmc1_ground_init                      false
% 3.63/0.99  --bmc1_pre_inst_next_state              false
% 3.63/0.99  --bmc1_pre_inst_state                   false
% 3.63/0.99  --bmc1_pre_inst_reach_state             false
% 3.63/0.99  --bmc1_out_unsat_core                   false
% 3.63/0.99  --bmc1_aig_witness_out                  false
% 3.63/0.99  --bmc1_verbose                          false
% 3.63/0.99  --bmc1_dump_clauses_tptp                false
% 3.63/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.99  --bmc1_dump_file                        -
% 3.63/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.99  --bmc1_ucm_extend_mode                  1
% 3.63/0.99  --bmc1_ucm_init_mode                    2
% 3.63/0.99  --bmc1_ucm_cone_mode                    none
% 3.63/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.99  --bmc1_ucm_relax_model                  4
% 3.63/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.99  --bmc1_ucm_layered_model                none
% 3.63/0.99  --bmc1_ucm_max_lemma_size               10
% 3.63/0.99  
% 3.63/0.99  ------ AIG Options
% 3.63/0.99  
% 3.63/0.99  --aig_mode                              false
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation Options
% 3.63/0.99  
% 3.63/0.99  --instantiation_flag                    true
% 3.63/0.99  --inst_sos_flag                         false
% 3.63/0.99  --inst_sos_phase                        true
% 3.63/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.99  --inst_lit_sel_side                     none
% 3.63/0.99  --inst_solver_per_active                1400
% 3.63/0.99  --inst_solver_calls_frac                1.
% 3.63/0.99  --inst_passive_queue_type               priority_queues
% 3.63/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.99  --inst_passive_queues_freq              [25;2]
% 3.63/0.99  --inst_dismatching                      true
% 3.63/0.99  --inst_eager_unprocessed_to_passive     true
% 3.63/0.99  --inst_prop_sim_given                   true
% 3.63/0.99  --inst_prop_sim_new                     false
% 3.63/0.99  --inst_subs_new                         false
% 3.63/0.99  --inst_eq_res_simp                      false
% 3.63/0.99  --inst_subs_given                       false
% 3.63/0.99  --inst_orphan_elimination               true
% 3.63/0.99  --inst_learning_loop_flag               true
% 3.63/0.99  --inst_learning_start                   3000
% 3.63/0.99  --inst_learning_factor                  2
% 3.63/0.99  --inst_start_prop_sim_after_learn       3
% 3.63/0.99  --inst_sel_renew                        solver
% 3.63/0.99  --inst_lit_activity_flag                true
% 3.63/0.99  --inst_restr_to_given                   false
% 3.63/0.99  --inst_activity_threshold               500
% 3.63/0.99  --inst_out_proof                        true
% 3.63/0.99  
% 3.63/0.99  ------ Resolution Options
% 3.63/0.99  
% 3.63/0.99  --resolution_flag                       false
% 3.63/0.99  --res_lit_sel                           adaptive
% 3.63/0.99  --res_lit_sel_side                      none
% 3.63/0.99  --res_ordering                          kbo
% 3.63/0.99  --res_to_prop_solver                    active
% 3.63/0.99  --res_prop_simpl_new                    false
% 3.63/0.99  --res_prop_simpl_given                  true
% 3.63/0.99  --res_passive_queue_type                priority_queues
% 3.63/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.99  --res_passive_queues_freq               [15;5]
% 3.63/0.99  --res_forward_subs                      full
% 3.63/0.99  --res_backward_subs                     full
% 3.63/0.99  --res_forward_subs_resolution           true
% 3.63/0.99  --res_backward_subs_resolution          true
% 3.63/0.99  --res_orphan_elimination                true
% 3.63/0.99  --res_time_limit                        2.
% 3.63/0.99  --res_out_proof                         true
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Options
% 3.63/0.99  
% 3.63/0.99  --superposition_flag                    true
% 3.63/0.99  --sup_passive_queue_type                priority_queues
% 3.63/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.99  --demod_completeness_check              fast
% 3.63/0.99  --demod_use_ground                      true
% 3.63/0.99  --sup_to_prop_solver                    passive
% 3.63/0.99  --sup_prop_simpl_new                    true
% 3.63/0.99  --sup_prop_simpl_given                  true
% 3.63/0.99  --sup_fun_splitting                     false
% 3.63/0.99  --sup_smt_interval                      50000
% 3.63/0.99  
% 3.63/0.99  ------ Superposition Simplification Setup
% 3.63/0.99  
% 3.63/0.99  --sup_indices_passive                   []
% 3.63/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_full_bw                           [BwDemod]
% 3.63/0.99  --sup_immed_triv                        [TrivRules]
% 3.63/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_immed_bw_main                     []
% 3.63/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.99  
% 3.63/0.99  ------ Combination Options
% 3.63/0.99  
% 3.63/0.99  --comb_res_mult                         3
% 3.63/0.99  --comb_sup_mult                         2
% 3.63/0.99  --comb_inst_mult                        10
% 3.63/0.99  
% 3.63/0.99  ------ Debug Options
% 3.63/0.99  
% 3.63/0.99  --dbg_backtrace                         false
% 3.63/0.99  --dbg_dump_prop_clauses                 false
% 3.63/0.99  --dbg_dump_prop_clauses_file            -
% 3.63/0.99  --dbg_out_stat                          false
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  ------ Proving...
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS status Theorem for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  fof(f6,axiom,(
% 3.63/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f12,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 3.63/0.99    inference(ennf_transformation,[],[f6])).
% 3.63/0.99  
% 3.63/0.99  fof(f18,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.63/0.99    inference(nnf_transformation,[],[f12])).
% 3.63/0.99  
% 3.63/0.99  fof(f19,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.63/0.99    inference(rectify,[],[f18])).
% 3.63/0.99  
% 3.63/0.99  fof(f22,plain,(
% 3.63/0.99    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f21,plain,(
% 3.63/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f20,plain,(
% 3.63/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f23,plain,(
% 3.63/0.99    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 3.63/0.99  
% 3.63/0.99  fof(f38,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f7,conjecture,(
% 3.63/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f8,negated_conjecture,(
% 3.63/0.99    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 3.63/0.99    inference(negated_conjecture,[],[f7])).
% 3.63/0.99  
% 3.63/0.99  fof(f13,plain,(
% 3.63/0.99    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 3.63/0.99    inference(ennf_transformation,[],[f8])).
% 3.63/0.99  
% 3.63/0.99  fof(f24,plain,(
% 3.63/0.99    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) & v1_relat_1(sK4))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f25,plain,(
% 3.63/0.99    k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) & v1_relat_1(sK4)),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f24])).
% 3.63/0.99  
% 3.63/0.99  fof(f40,plain,(
% 3.63/0.99    v1_relat_1(sK4)),
% 3.63/0.99    inference(cnf_transformation,[],[f25])).
% 3.63/0.99  
% 3.63/0.99  fof(f5,axiom,(
% 3.63/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f17,plain,(
% 3.63/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.63/0.99    inference(nnf_transformation,[],[f5])).
% 3.63/0.99  
% 3.63/0.99  fof(f33,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.63/0.99    inference(cnf_transformation,[],[f17])).
% 3.63/0.99  
% 3.63/0.99  fof(f4,axiom,(
% 3.63/0.99    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f11,plain,(
% 3.63/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.63/0.99    inference(ennf_transformation,[],[f4])).
% 3.63/0.99  
% 3.63/0.99  fof(f31,plain,(
% 3.63/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.63/0.99    inference(cnf_transformation,[],[f11])).
% 3.63/0.99  
% 3.63/0.99  fof(f1,axiom,(
% 3.63/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f14,plain,(
% 3.63/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.63/0.99    inference(nnf_transformation,[],[f1])).
% 3.63/0.99  
% 3.63/0.99  fof(f26,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f14])).
% 3.63/0.99  
% 3.63/0.99  fof(f3,axiom,(
% 3.63/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f30,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f3])).
% 3.63/0.99  
% 3.63/0.99  fof(f43,plain,(
% 3.63/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.63/0.99    inference(definition_unfolding,[],[f26,f30])).
% 3.63/0.99  
% 3.63/0.99  fof(f41,plain,(
% 3.63/0.99    k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0)),
% 3.63/0.99    inference(cnf_transformation,[],[f25])).
% 3.63/0.99  
% 3.63/0.99  fof(f2,axiom,(
% 3.63/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.63/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.99  
% 3.63/0.99  fof(f9,plain,(
% 3.63/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.63/0.99    inference(rectify,[],[f2])).
% 3.63/0.99  
% 3.63/0.99  fof(f10,plain,(
% 3.63/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.63/0.99    inference(ennf_transformation,[],[f9])).
% 3.63/0.99  
% 3.63/0.99  fof(f15,plain,(
% 3.63/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.63/0.99    introduced(choice_axiom,[])).
% 3.63/0.99  
% 3.63/0.99  fof(f16,plain,(
% 3.63/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.63/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).
% 3.63/0.99  
% 3.63/0.99  fof(f29,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.63/0.99    inference(cnf_transformation,[],[f16])).
% 3.63/0.99  
% 3.63/0.99  fof(f44,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.63/0.99    inference(definition_unfolding,[],[f29,f30])).
% 3.63/0.99  
% 3.63/0.99  fof(f32,plain,(
% 3.63/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f17])).
% 3.63/0.99  
% 3.63/0.99  fof(f46,plain,(
% 3.63/0.99    ( ! [X1] : (k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1)) )),
% 3.63/0.99    inference(equality_resolution,[],[f32])).
% 3.63/0.99  
% 3.63/0.99  fof(f37,plain,(
% 3.63/0.99    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f36,plain,(
% 3.63/0.99    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f47,plain,(
% 3.63/0.99    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(equality_resolution,[],[f36])).
% 3.63/0.99  
% 3.63/0.99  fof(f35,plain,(
% 3.63/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f48,plain,(
% 3.63/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(equality_resolution,[],[f35])).
% 3.63/0.99  
% 3.63/0.99  fof(f34,plain,(
% 3.63/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  fof(f49,plain,(
% 3.63/0.99    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) | ~r2_hidden(X6,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(equality_resolution,[],[f34])).
% 3.63/0.99  
% 3.63/0.99  fof(f39,plain,(
% 3.63/0.99    ( ! [X4,X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) | ~r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 3.63/0.99    inference(cnf_transformation,[],[f23])).
% 3.63/0.99  
% 3.63/0.99  cnf(c_8,plain,
% 3.63/0.99      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.63/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.63/0.99      | ~ v1_relat_1(X0)
% 3.63/0.99      | k10_relat_1(X0,X1) = X2 ),
% 3.63/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_14,negated_conjecture,
% 3.63/0.99      ( v1_relat_1(sK4) ),
% 3.63/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_268,plain,
% 3.63/0.99      ( r2_hidden(sK2(X0,X1,X2),X1)
% 3.63/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.63/0.99      | k10_relat_1(X0,X1) = X2
% 3.63/0.99      | sK4 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_269,plain,
% 3.63/0.99      ( r2_hidden(sK2(sK4,X0,X1),X0)
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.63/0.99      | k10_relat_1(sK4,X0) = X1 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_268]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_851,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_5,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_tarski(X1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4,plain,
% 3.63/0.99      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_853,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1,plain,
% 3.63/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.63/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.63/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_856,plain,
% 3.63/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.63/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1278,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_853,c_856]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1528,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_5,c_1278]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_13,negated_conjecture,
% 3.63/0.99      ( k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1771,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) != k1_xboole_0
% 3.63/0.99      | k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1528,c_13]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1772,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != X0 ),
% 3.63/0.99      inference(equality_factoring,[status(thm)],[c_1528]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1790,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_xboole_0 ),
% 3.63/0.99      inference(forward_subsumption_resolution,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1772,c_1528]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1794,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1790]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2987,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1771,c_1794]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.63/0.99      | ~ r1_xboole_0(X1,X2) ),
% 3.63/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_855,plain,
% 3.63/0.99      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.63/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_4691,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top
% 3.63/0.99      | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_5,c_855]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_36,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17506,plain,
% 3.63/0.99      ( r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top
% 3.63/0.99      | X0 = X1 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_4691,c_36]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17507,plain,
% 3.63/0.99      ( X0 = X1
% 3.63/0.99      | r2_hidden(X2,k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) != iProver_top ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_17506]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17521,plain,
% 3.63/0.99      ( k1_xboole_0 = X0 | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_2987,c_17507]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_539,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_969,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) != X0
% 3.63/0.99      | k1_xboole_0 != X0
% 3.63/0.99      | k1_xboole_0 = k10_relat_1(sK4,k1_xboole_0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_539]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1729,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != X0 ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1528,c_13]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_6,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
% 3.63/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_34,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) != k1_tarski(k1_xboole_0) ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_35,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0)
% 3.63/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_2586,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0
% 3.63/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_3008,plain,
% 3.63/0.99      ( k4_xboole_0(k1_tarski(k10_relat_1(sK4,k1_xboole_0)),k1_tarski(k10_relat_1(sK4,k1_xboole_0))) = k1_xboole_0 ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_1729,c_34,c_35,c_2586]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_17522,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = X0
% 3.63/0.99      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_3008,c_17507]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19554,plain,
% 3.63/0.99      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(global_propositional_subsumption,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_17521,c_13,c_969,c_17522]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19555,plain,
% 3.63/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(renaming,[status(thm)],[c_19554]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19563,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = X0
% 3.63/0.99      | r2_hidden(sK1(sK4,k1_xboole_0,X0),X0) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_851,c_19555]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19588,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_19563]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19562,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK2(sK4,X0,k1_xboole_0),X0) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_851,c_19555]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19585,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK2(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_19562]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_9,plain,
% 3.63/0.99      ( r2_hidden(sK1(X0,X1,X2),X2)
% 3.63/0.99      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
% 3.63/0.99      | ~ v1_relat_1(X0)
% 3.63/0.99      | k10_relat_1(X0,X1) = X2 ),
% 3.63/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_253,plain,
% 3.63/0.99      ( r2_hidden(sK1(X0,X1,X2),X2)
% 3.63/0.99      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
% 3.63/0.99      | k10_relat_1(X0,X1) = X2
% 3.63/0.99      | sK4 != X0 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_254,plain,
% 3.63/0.99      ( r2_hidden(sK1(sK4,X0,X1),X1)
% 3.63/0.99      | r2_hidden(k4_tarski(sK1(sK4,X0,X1),sK2(sK4,X0,X1)),sK4)
% 3.63/0.99      | k10_relat_1(sK4,X0) = X1 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_253]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_852,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top
% 3.63/0.99      | r2_hidden(k4_tarski(sK1(sK4,X0,X1),sK2(sK4,X0,X1)),sK4) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_10,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.63/0.99      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.63/0.99      | ~ v1_relat_1(X3) ),
% 3.63/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_301,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | r2_hidden(X2,k10_relat_1(X3,X1))
% 3.63/0.99      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 3.63/0.99      | sK4 != X3 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_302,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | r2_hidden(X2,k10_relat_1(sK4,X1))
% 3.63/0.99      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_849,plain,
% 3.63/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.63/0.99      | r2_hidden(X2,k10_relat_1(sK4,X1)) = iProver_top
% 3.63/0.99      | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1150,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(sK2(sK4,X0,X1),X2) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) = iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X2)) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_852,c_849]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19561,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK2(sK4,X0,k1_xboole_0),X1) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,k1_xboole_0),k10_relat_1(sK4,X1)) = iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_1150,c_19555]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_19582,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK2(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_19561]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_11,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.63/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.63/0.99      | ~ v1_relat_1(X1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_328,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.63/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.63/0.99      | sK4 != X1 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_329,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 3.63/0.99      | r2_hidden(sK3(sK4,X1,X0),X1) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_847,plain,
% 3.63/0.99      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 3.63/0.99      | r2_hidden(sK3(sK4,X1,X0),X1) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_12,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.63/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X2,X0)),X1)
% 3.63/0.99      | ~ v1_relat_1(X1) ),
% 3.63/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_316,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.63/0.99      | r2_hidden(k4_tarski(X0,sK3(X1,X2,X0)),X1)
% 3.63/0.99      | sK4 != X1 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_317,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 3.63/0.99      | r2_hidden(k4_tarski(X0,sK3(sK4,X1,X0)),sK4) ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_848,plain,
% 3.63/0.99      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 3.63/0.99      | r2_hidden(k4_tarski(X0,sK3(sK4,X1,X0)),sK4) = iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_7,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | ~ r2_hidden(sK1(X2,X1,X3),X3)
% 3.63/0.99      | ~ r2_hidden(k4_tarski(sK1(X2,X1,X3),X0),X2)
% 3.63/0.99      | ~ v1_relat_1(X2)
% 3.63/0.99      | k10_relat_1(X2,X1) = X3 ),
% 3.63/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_283,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | ~ r2_hidden(sK1(X2,X1,X3),X3)
% 3.63/0.99      | ~ r2_hidden(k4_tarski(sK1(X2,X1,X3),X0),X2)
% 3.63/0.99      | k10_relat_1(X2,X1) = X3
% 3.63/0.99      | sK4 != X2 ),
% 3.63/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_284,plain,
% 3.63/0.99      ( ~ r2_hidden(X0,X1)
% 3.63/0.99      | ~ r2_hidden(sK1(sK4,X1,X2),X2)
% 3.63/0.99      | ~ r2_hidden(k4_tarski(sK1(sK4,X1,X2),X0),sK4)
% 3.63/0.99      | k10_relat_1(sK4,X1) = X2 ),
% 3.63/0.99      inference(unflattening,[status(thm)],[c_283]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_850,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
% 3.63/0.99      | r2_hidden(k4_tarski(sK1(sK4,X0,X1),X2),sK4) != iProver_top ),
% 3.63/0.99      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1061,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(sK3(sK4,X2,sK1(sK4,X0,X1)),X0) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X2)) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_848,c_850]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1349,plain,
% 3.63/0.99      ( k10_relat_1(sK4,X0) = X1
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),X1) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,X0,X1),k10_relat_1(sK4,X0)) != iProver_top ),
% 3.63/0.99      inference(superposition,[status(thm)],[c_847,c_1061]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_1351,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 3.63/0.99      | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) != iProver_top
% 3.63/0.99      | r2_hidden(sK1(sK4,k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_1349]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(c_970,plain,
% 3.63/0.99      ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 3.63/0.99      | k1_xboole_0 = k10_relat_1(sK4,k1_xboole_0)
% 3.63/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.63/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 3.63/0.99  
% 3.63/0.99  cnf(contradiction,plain,
% 3.63/0.99      ( $false ),
% 3.63/0.99      inference(minisat,
% 3.63/0.99                [status(thm)],
% 3.63/0.99                [c_19588,c_19585,c_19582,c_1351,c_970,c_35,c_34,c_13]) ).
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.99  
% 3.63/0.99  ------                               Statistics
% 3.63/0.99  
% 3.63/0.99  ------ General
% 3.63/0.99  
% 3.63/0.99  abstr_ref_over_cycles:                  0
% 3.63/0.99  abstr_ref_under_cycles:                 0
% 3.63/0.99  gc_basic_clause_elim:                   0
% 3.63/0.99  forced_gc_time:                         0
% 3.63/0.99  parsing_time:                           0.011
% 3.63/0.99  unif_index_cands_time:                  0.
% 3.63/0.99  unif_index_add_time:                    0.
% 3.63/0.99  orderings_time:                         0.
% 3.63/0.99  out_proof_time:                         0.01
% 3.63/0.99  total_time:                             0.477
% 3.63/0.99  num_of_symbols:                         44
% 3.63/0.99  num_of_terms:                           14703
% 3.63/0.99  
% 3.63/0.99  ------ Preprocessing
% 3.63/0.99  
% 3.63/0.99  num_of_splits:                          0
% 3.63/0.99  num_of_split_atoms:                     0
% 3.63/0.99  num_of_reused_defs:                     0
% 3.63/0.99  num_eq_ax_congr_red:                    30
% 3.63/0.99  num_of_sem_filtered_clauses:            1
% 3.63/0.99  num_of_subtypes:                        0
% 3.63/0.99  monotx_restored_types:                  0
% 3.63/0.99  sat_num_of_epr_types:                   0
% 3.63/0.99  sat_num_of_non_cyclic_types:            0
% 3.63/0.99  sat_guarded_non_collapsed_types:        0
% 3.63/0.99  num_pure_diseq_elim:                    0
% 3.63/0.99  simp_replaced_by:                       0
% 3.63/0.99  res_preprocessed:                       78
% 3.63/0.99  prep_upred:                             0
% 3.63/0.99  prep_unflattend:                        22
% 3.63/0.99  smt_new_axioms:                         0
% 3.63/0.99  pred_elim_cands:                        2
% 3.63/0.99  pred_elim:                              1
% 3.63/0.99  pred_elim_cl:                           1
% 3.63/0.99  pred_elim_cycles:                       4
% 3.63/0.99  merged_defs:                            8
% 3.63/0.99  merged_defs_ncl:                        0
% 3.63/0.99  bin_hyper_res:                          8
% 3.63/0.99  prep_cycles:                            4
% 3.63/0.99  pred_elim_time:                         0.004
% 3.63/0.99  splitting_time:                         0.
% 3.63/0.99  sem_filter_time:                        0.
% 3.63/0.99  monotx_time:                            0.
% 3.63/0.99  subtype_inf_time:                       0.
% 3.63/0.99  
% 3.63/0.99  ------ Problem properties
% 3.63/0.99  
% 3.63/0.99  clauses:                                14
% 3.63/0.99  conjectures:                            1
% 3.63/0.99  epr:                                    0
% 3.63/0.99  horn:                                   9
% 3.63/0.99  ground:                                 1
% 3.63/0.99  unary:                                  2
% 3.63/0.99  binary:                                 8
% 3.63/0.99  lits:                                   31
% 3.63/0.99  lits_eq:                                10
% 3.63/0.99  fd_pure:                                0
% 3.63/0.99  fd_pseudo:                              0
% 3.63/0.99  fd_cond:                                0
% 3.63/0.99  fd_pseudo_cond:                         5
% 3.63/0.99  ac_symbols:                             0
% 3.63/0.99  
% 3.63/0.99  ------ Propositional Solver
% 3.63/0.99  
% 3.63/0.99  prop_solver_calls:                      29
% 3.63/0.99  prop_fast_solver_calls:                 697
% 3.63/0.99  smt_solver_calls:                       0
% 3.63/0.99  smt_fast_solver_calls:                  0
% 3.63/0.99  prop_num_of_clauses:                    4429
% 3.63/0.99  prop_preprocess_simplified:             9373
% 3.63/0.99  prop_fo_subsumed:                       29
% 3.63/0.99  prop_solver_time:                       0.
% 3.63/0.99  smt_solver_time:                        0.
% 3.63/0.99  smt_fast_solver_time:                   0.
% 3.63/0.99  prop_fast_solver_time:                  0.
% 3.63/0.99  prop_unsat_core_time:                   0.
% 3.63/0.99  
% 3.63/0.99  ------ QBF
% 3.63/0.99  
% 3.63/0.99  qbf_q_res:                              0
% 3.63/0.99  qbf_num_tautologies:                    0
% 3.63/0.99  qbf_prep_cycles:                        0
% 3.63/0.99  
% 3.63/0.99  ------ BMC1
% 3.63/0.99  
% 3.63/0.99  bmc1_current_bound:                     -1
% 3.63/0.99  bmc1_last_solved_bound:                 -1
% 3.63/0.99  bmc1_unsat_core_size:                   -1
% 3.63/0.99  bmc1_unsat_core_parents_size:           -1
% 3.63/0.99  bmc1_merge_next_fun:                    0
% 3.63/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.99  
% 3.63/0.99  ------ Instantiation
% 3.63/0.99  
% 3.63/0.99  inst_num_of_clauses:                    978
% 3.63/0.99  inst_num_in_passive:                    593
% 3.63/0.99  inst_num_in_active:                     308
% 3.63/0.99  inst_num_in_unprocessed:                77
% 3.63/0.99  inst_num_of_loops:                      430
% 3.63/0.99  inst_num_of_learning_restarts:          0
% 3.63/0.99  inst_num_moves_active_passive:          120
% 3.63/0.99  inst_lit_activity:                      0
% 3.63/0.99  inst_lit_activity_moves:                0
% 3.63/0.99  inst_num_tautologies:                   0
% 3.63/0.99  inst_num_prop_implied:                  0
% 3.63/0.99  inst_num_existing_simplified:           0
% 3.63/0.99  inst_num_eq_res_simplified:             0
% 3.63/0.99  inst_num_child_elim:                    0
% 3.63/0.99  inst_num_of_dismatching_blockings:      585
% 3.63/0.99  inst_num_of_non_proper_insts:           1222
% 3.63/0.99  inst_num_of_duplicates:                 0
% 3.63/0.99  inst_inst_num_from_inst_to_res:         0
% 3.63/0.99  inst_dismatching_checking_time:         0.
% 3.63/0.99  
% 3.63/0.99  ------ Resolution
% 3.63/0.99  
% 3.63/0.99  res_num_of_clauses:                     0
% 3.63/0.99  res_num_in_passive:                     0
% 3.63/0.99  res_num_in_active:                      0
% 3.63/0.99  res_num_of_loops:                       82
% 3.63/0.99  res_forward_subset_subsumed:            57
% 3.63/0.99  res_backward_subset_subsumed:           2
% 3.63/0.99  res_forward_subsumed:                   0
% 3.63/0.99  res_backward_subsumed:                  0
% 3.63/0.99  res_forward_subsumption_resolution:     0
% 3.63/0.99  res_backward_subsumption_resolution:    0
% 3.63/0.99  res_clause_to_clause_subsumption:       8318
% 3.63/0.99  res_orphan_elimination:                 0
% 3.63/0.99  res_tautology_del:                      116
% 3.63/0.99  res_num_eq_res_simplified:              0
% 3.63/0.99  res_num_sel_changes:                    0
% 3.63/0.99  res_moves_from_active_to_pass:          0
% 3.63/0.99  
% 3.63/0.99  ------ Superposition
% 3.63/0.99  
% 3.63/0.99  sup_time_total:                         0.
% 3.63/0.99  sup_time_generating:                    0.
% 3.63/0.99  sup_time_sim_full:                      0.
% 3.63/0.99  sup_time_sim_immed:                     0.
% 3.63/0.99  
% 3.63/0.99  sup_num_of_clauses:                     730
% 3.63/0.99  sup_num_in_active:                      79
% 3.63/0.99  sup_num_in_passive:                     651
% 3.63/0.99  sup_num_of_loops:                       85
% 3.63/0.99  sup_fw_superposition:                   574
% 3.63/0.99  sup_bw_superposition:                   1757
% 3.63/0.99  sup_immediate_simplified:               990
% 3.63/0.99  sup_given_eliminated:                   5
% 3.63/0.99  comparisons_done:                       0
% 3.63/0.99  comparisons_avoided:                    33
% 3.63/0.99  
% 3.63/0.99  ------ Simplifications
% 3.63/0.99  
% 3.63/0.99  
% 3.63/0.99  sim_fw_subset_subsumed:                 542
% 3.63/0.99  sim_bw_subset_subsumed:                 28
% 3.63/0.99  sim_fw_subsumed:                        194
% 3.63/0.99  sim_bw_subsumed:                        280
% 3.63/0.99  sim_fw_subsumption_res:                 37
% 3.63/0.99  sim_bw_subsumption_res:                 43
% 3.63/0.99  sim_tautology_del:                      7
% 3.63/0.99  sim_eq_tautology_del:                   80
% 3.63/0.99  sim_eq_res_simp:                        3
% 3.63/0.99  sim_fw_demodulated:                     2
% 3.63/0.99  sim_bw_demodulated:                     0
% 3.63/0.99  sim_light_normalised:                   5
% 3.63/0.99  sim_joinable_taut:                      0
% 3.63/0.99  sim_joinable_simp:                      0
% 3.63/0.99  sim_ac_normalised:                      0
% 3.63/0.99  sim_smt_subsumption:                    0
% 3.63/0.99  
%------------------------------------------------------------------------------
