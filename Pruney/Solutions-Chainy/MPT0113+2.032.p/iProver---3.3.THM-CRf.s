%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:47 EST 2020

% Result     : Theorem 23.29s
% Output     : CNFRefutation 23.29s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 369 expanded)
%              Number of clauses        :   65 ( 142 expanded)
%              Number of leaves         :   17 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  275 ( 704 expanded)
%              Number of equality atoms :  106 ( 308 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f25])).

fof(f45,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f43,f39,f39])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f46,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1112,plain,
    ( ~ r2_hidden(sK1(sK2,sK4),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))
    | ~ r2_hidden(sK1(sK2,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_86244,plain,
    ( ~ r2_hidden(sK1(sK2,sK4),k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)))
    | ~ r2_hidden(sK1(sK2,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_799,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_966,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_799])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_802,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1277,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_966,c_802])).

cnf(c_15,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_801,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1184,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_801])).

cnf(c_2211,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1184])).

cnf(c_12684,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2211])).

cnf(c_22247,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_12684])).

cnf(c_22802,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_22247,c_802])).

cnf(c_12,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_803,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1275,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_803,c_802])).

cnf(c_27644,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1275])).

cnf(c_28535,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) ),
    inference(superposition,[status(thm)],[c_1277,c_27644])).

cnf(c_28855,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_28535,c_1277])).

cnf(c_1180,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_15])).

cnf(c_29998,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_28855,c_1180])).

cnf(c_31583,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK3,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_22802,c_29998])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12663,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_2211])).

cnf(c_13180,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_12663,c_802])).

cnf(c_1182,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_15])).

cnf(c_21691,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1277,c_1182])).

cnf(c_23025,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_13180,c_21691])).

cnf(c_23219,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_23025,c_13180])).

cnf(c_23220,plain,
    ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23219,c_16])).

cnf(c_31796,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31583,c_16,c_23220,c_27644])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1130,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(sK2,sK4),sK2)
    | X0 != sK1(sK2,sK4)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_5903,plain,
    ( r2_hidden(sK1(sK2,sK4),X0)
    | ~ r2_hidden(sK1(sK2,sK4),sK2)
    | X0 != sK2
    | sK1(sK2,sK4) != sK1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_14678,plain,
    ( r2_hidden(sK1(sK2,sK4),k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)))
    | ~ r2_hidden(sK1(sK2,sK4),sK2)
    | sK1(sK2,sK4) != sK1(sK2,sK4)
    | k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) != sK2 ),
    inference(instantiation,[status(thm)],[c_5903])).

cnf(c_6349,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_388,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1433,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_2928,plain,
    ( X0 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
    | X0 = sK2
    | sK2 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_6348,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
    | k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) = sK2
    | sK2 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_387,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2582,plain,
    ( sK1(X0,X1) = sK1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_5904,plain,
    ( sK1(sK2,sK4) = sK1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2582])).

cnf(c_1050,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_1160,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1425,plain,
    ( k3_xboole_0(sK2,X0) != sK2
    | sK2 = k3_xboole_0(sK2,X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_2592,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) != sK2
    | sK2 = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_1045,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_943,plain,
    ( r1_xboole_0(sK2,sK4)
    | r2_hidden(sK1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_940,plain,
    ( r1_xboole_0(sK2,sK4)
    | r2_hidden(sK1(sK2,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_323,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != X0
    | k3_xboole_0(X1,X0) = X1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_324,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = sK2 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_130,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_313,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_130,c_17])).

cnf(c_314,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86244,c_31796,c_14678,c_6349,c_6348,c_5904,c_2592,c_1045,c_943,c_940,c_324,c_314])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.29/3.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.29/3.50  
% 23.29/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.29/3.50  
% 23.29/3.50  ------  iProver source info
% 23.29/3.50  
% 23.29/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.29/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.29/3.50  git: non_committed_changes: false
% 23.29/3.50  git: last_make_outside_of_git: false
% 23.29/3.50  
% 23.29/3.50  ------ 
% 23.29/3.50  ------ Parsing...
% 23.29/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.29/3.50  
% 23.29/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.29/3.50  
% 23.29/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.29/3.50  
% 23.29/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.29/3.50  ------ Proving...
% 23.29/3.50  ------ Problem Properties 
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  clauses                                 19
% 23.29/3.50  conjectures                             2
% 23.29/3.50  EPR                                     2
% 23.29/3.50  Horn                                    13
% 23.29/3.50  unary                                   6
% 23.29/3.50  binary                                  8
% 23.29/3.50  lits                                    38
% 23.29/3.50  lits eq                                 9
% 23.29/3.50  fd_pure                                 0
% 23.29/3.50  fd_pseudo                               0
% 23.29/3.50  fd_cond                                 0
% 23.29/3.50  fd_pseudo_cond                          3
% 23.29/3.50  AC symbols                              0
% 23.29/3.50  
% 23.29/3.50  ------ Input Options Time Limit: Unbounded
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  ------ 
% 23.29/3.50  Current options:
% 23.29/3.50  ------ 
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  ------ Proving...
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  % SZS status Theorem for theBenchmark.p
% 23.29/3.50  
% 23.29/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.29/3.50  
% 23.29/3.50  fof(f2,axiom,(
% 23.29/3.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f17,plain,(
% 23.29/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.29/3.50    inference(nnf_transformation,[],[f2])).
% 23.29/3.50  
% 23.29/3.50  fof(f18,plain,(
% 23.29/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.29/3.50    inference(flattening,[],[f17])).
% 23.29/3.50  
% 23.29/3.50  fof(f19,plain,(
% 23.29/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.29/3.50    inference(rectify,[],[f18])).
% 23.29/3.50  
% 23.29/3.50  fof(f20,plain,(
% 23.29/3.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.29/3.50    introduced(choice_axiom,[])).
% 23.29/3.50  
% 23.29/3.50  fof(f21,plain,(
% 23.29/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.29/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 23.29/3.50  
% 23.29/3.50  fof(f29,plain,(
% 23.29/3.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.29/3.50    inference(cnf_transformation,[],[f21])).
% 23.29/3.50  
% 23.29/3.50  fof(f5,axiom,(
% 23.29/3.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f39,plain,(
% 23.29/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.29/3.50    inference(cnf_transformation,[],[f5])).
% 23.29/3.50  
% 23.29/3.50  fof(f51,plain,(
% 23.29/3.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 23.29/3.50    inference(definition_unfolding,[],[f29,f39])).
% 23.29/3.50  
% 23.29/3.50  fof(f59,plain,(
% 23.29/3.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.29/3.50    inference(equality_resolution,[],[f51])).
% 23.29/3.50  
% 23.29/3.50  fof(f1,axiom,(
% 23.29/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f27,plain,(
% 23.29/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f1])).
% 23.29/3.50  
% 23.29/3.50  fof(f11,conjecture,(
% 23.29/3.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f12,negated_conjecture,(
% 23.29/3.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.29/3.50    inference(negated_conjecture,[],[f11])).
% 23.29/3.50  
% 23.29/3.50  fof(f16,plain,(
% 23.29/3.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.29/3.50    inference(ennf_transformation,[],[f12])).
% 23.29/3.50  
% 23.29/3.50  fof(f25,plain,(
% 23.29/3.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 23.29/3.50    introduced(choice_axiom,[])).
% 23.29/3.50  
% 23.29/3.50  fof(f26,plain,(
% 23.29/3.50    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 23.29/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f25])).
% 23.29/3.50  
% 23.29/3.50  fof(f45,plain,(
% 23.29/3.50    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 23.29/3.50    inference(cnf_transformation,[],[f26])).
% 23.29/3.50  
% 23.29/3.50  fof(f57,plain,(
% 23.29/3.50    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))),
% 23.29/3.50    inference(definition_unfolding,[],[f45,f39])).
% 23.29/3.50  
% 23.29/3.50  fof(f7,axiom,(
% 23.29/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f15,plain,(
% 23.29/3.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.29/3.50    inference(ennf_transformation,[],[f7])).
% 23.29/3.50  
% 23.29/3.50  fof(f41,plain,(
% 23.29/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f15])).
% 23.29/3.50  
% 23.29/3.50  fof(f9,axiom,(
% 23.29/3.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f43,plain,(
% 23.29/3.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f9])).
% 23.29/3.50  
% 23.29/3.50  fof(f56,plain,(
% 23.29/3.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 23.29/3.50    inference(definition_unfolding,[],[f43,f39,f39])).
% 23.29/3.50  
% 23.29/3.50  fof(f8,axiom,(
% 23.29/3.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f42,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f8])).
% 23.29/3.50  
% 23.29/3.50  fof(f55,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 23.29/3.50    inference(definition_unfolding,[],[f42,f39])).
% 23.29/3.50  
% 23.29/3.50  fof(f6,axiom,(
% 23.29/3.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f40,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f6])).
% 23.29/3.50  
% 23.29/3.50  fof(f10,axiom,(
% 23.29/3.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f44,plain,(
% 23.29/3.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f10])).
% 23.29/3.50  
% 23.29/3.50  fof(f3,axiom,(
% 23.29/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f13,plain,(
% 23.29/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.29/3.50    inference(rectify,[],[f3])).
% 23.29/3.50  
% 23.29/3.50  fof(f14,plain,(
% 23.29/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.29/3.50    inference(ennf_transformation,[],[f13])).
% 23.29/3.50  
% 23.29/3.50  fof(f22,plain,(
% 23.29/3.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 23.29/3.50    introduced(choice_axiom,[])).
% 23.29/3.50  
% 23.29/3.50  fof(f23,plain,(
% 23.29/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.29/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f22])).
% 23.29/3.50  
% 23.29/3.50  fof(f34,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f23])).
% 23.29/3.50  
% 23.29/3.50  fof(f35,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 23.29/3.50    inference(cnf_transformation,[],[f23])).
% 23.29/3.50  
% 23.29/3.50  fof(f4,axiom,(
% 23.29/3.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.29/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.29/3.50  
% 23.29/3.50  fof(f24,plain,(
% 23.29/3.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.29/3.50    inference(nnf_transformation,[],[f4])).
% 23.29/3.50  
% 23.29/3.50  fof(f37,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.29/3.50    inference(cnf_transformation,[],[f24])).
% 23.29/3.50  
% 23.29/3.50  fof(f54,plain,(
% 23.29/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.29/3.50    inference(definition_unfolding,[],[f37,f39])).
% 23.29/3.50  
% 23.29/3.50  fof(f46,plain,(
% 23.29/3.50    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 23.29/3.50    inference(cnf_transformation,[],[f26])).
% 23.29/3.50  
% 23.29/3.50  cnf(c_5,plain,
% 23.29/3.50      ( ~ r2_hidden(X0,X1)
% 23.29/3.50      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 23.29/3.50      inference(cnf_transformation,[],[f59]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1112,plain,
% 23.29/3.50      ( ~ r2_hidden(sK1(sK2,sK4),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))
% 23.29/3.50      | ~ r2_hidden(sK1(sK2,sK4),sK4) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_86244,plain,
% 23.29/3.50      ( ~ r2_hidden(sK1(sK2,sK4),k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)))
% 23.29/3.50      | ~ r2_hidden(sK1(sK2,sK4),sK4) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1112]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_0,plain,
% 23.29/3.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.29/3.50      inference(cnf_transformation,[],[f27]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_18,negated_conjecture,
% 23.29/3.50      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 23.29/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_799,plain,
% 23.29/3.50      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
% 23.29/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_966,plain,
% 23.29/3.50      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
% 23.29/3.50      inference(demodulation,[status(thm)],[c_0,c_799]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_13,plain,
% 23.29/3.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.29/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_802,plain,
% 23.29/3.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.29/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1277,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_966,c_802]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_15,plain,
% 23.29/3.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.29/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_14,plain,
% 23.29/3.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 23.29/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_801,plain,
% 23.29/3.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.29/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1184,plain,
% 23.29/3.50      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_15,c_801]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_2211,plain,
% 23.29/3.50      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_0,c_1184]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_12684,plain,
% 23.29/3.50      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_0,c_2211]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_22247,plain,
% 23.29/3.50      ( r1_tarski(sK2,k3_xboole_0(sK3,sK2)) = iProver_top ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_1277,c_12684]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_22802,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = sK2 ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_22247,c_802]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_12,plain,
% 23.29/3.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 23.29/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_803,plain,
% 23.29/3.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 23.29/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1275,plain,
% 23.29/3.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_803,c_802]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_27644,plain,
% 23.29/3.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_0,c_1275]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_28535,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_1277,c_27644]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_28855,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2) = sK2 ),
% 23.29/3.50      inference(light_normalisation,[status(thm)],[c_28535,c_1277]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1180,plain,
% 23.29/3.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_0,c_15]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_29998,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k3_xboole_0(X0,sK2)) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_28855,c_1180]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_31583,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK3,sK2),sK2)) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_22802,c_29998]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_16,plain,
% 23.29/3.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.29/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_12663,plain,
% 23.29/3.50      ( r1_tarski(sK2,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_1277,c_2211]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_13180,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_12663,c_802]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1182,plain,
% 23.29/3.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_0,c_15]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_21691,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_1277,c_1182]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_23025,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 23.29/3.50      inference(superposition,[status(thm)],[c_13180,c_21691]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_23219,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,sK2) ),
% 23.29/3.50      inference(light_normalisation,[status(thm)],[c_23025,c_13180]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_23220,plain,
% 23.29/3.50      ( k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),k1_xboole_0) = k1_xboole_0 ),
% 23.29/3.50      inference(demodulation,[status(thm)],[c_23219,c_16]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_31796,plain,
% 23.29/3.50      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 23.29/3.50      inference(demodulation,
% 23.29/3.50                [status(thm)],
% 23.29/3.50                [c_31583,c_16,c_23220,c_27644]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_391,plain,
% 23.29/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.29/3.50      theory(equality) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1130,plain,
% 23.29/3.50      ( r2_hidden(X0,X1)
% 23.29/3.50      | ~ r2_hidden(sK1(sK2,sK4),sK2)
% 23.29/3.50      | X0 != sK1(sK2,sK4)
% 23.29/3.50      | X1 != sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_391]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_5903,plain,
% 23.29/3.50      ( r2_hidden(sK1(sK2,sK4),X0)
% 23.29/3.50      | ~ r2_hidden(sK1(sK2,sK4),sK2)
% 23.29/3.50      | X0 != sK2
% 23.29/3.50      | sK1(sK2,sK4) != sK1(sK2,sK4) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1130]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_14678,plain,
% 23.29/3.50      ( r2_hidden(sK1(sK2,sK4),k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)))
% 23.29/3.50      | ~ r2_hidden(sK1(sK2,sK4),sK2)
% 23.29/3.50      | sK1(sK2,sK4) != sK1(sK2,sK4)
% 23.29/3.50      | k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) != sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_5903]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_6349,plain,
% 23.29/3.50      ( k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_15]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_388,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1433,plain,
% 23.29/3.50      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_388]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_2928,plain,
% 23.29/3.50      ( X0 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
% 23.29/3.50      | X0 = sK2
% 23.29/3.50      | sK2 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1433]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_6348,plain,
% 23.29/3.50      ( k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
% 23.29/3.50      | k5_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(k3_xboole_0(sK2,sK3),sK4)) = sK2
% 23.29/3.50      | sK2 != k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_2928]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_387,plain,( X0 = X0 ),theory(equality) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_2582,plain,
% 23.29/3.50      ( sK1(X0,X1) = sK1(X0,X1) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_387]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_5904,plain,
% 23.29/3.50      ( sK1(sK2,sK4) = sK1(sK2,sK4) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_2582]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1050,plain,
% 23.29/3.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_388]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1160,plain,
% 23.29/3.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1050]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1425,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,X0) != sK2
% 23.29/3.50      | sK2 = k3_xboole_0(sK2,X0)
% 23.29/3.50      | sK2 != sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1160]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_2592,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) != sK2
% 23.29/3.50      | sK2 = k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))
% 23.29/3.50      | sK2 != sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_1425]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_1045,plain,
% 23.29/3.50      ( sK2 = sK2 ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_387]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_9,plain,
% 23.29/3.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 23.29/3.50      inference(cnf_transformation,[],[f34]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_943,plain,
% 23.29/3.50      ( r1_xboole_0(sK2,sK4) | r2_hidden(sK1(sK2,sK4),sK2) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_8,plain,
% 23.29/3.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 23.29/3.50      inference(cnf_transformation,[],[f35]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_940,plain,
% 23.29/3.50      ( r1_xboole_0(sK2,sK4) | r2_hidden(sK1(sK2,sK4),sK4) ),
% 23.29/3.50      inference(instantiation,[status(thm)],[c_8]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_323,plain,
% 23.29/3.50      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)) != X0
% 23.29/3.50      | k3_xboole_0(X1,X0) = X1
% 23.29/3.50      | sK2 != X1 ),
% 23.29/3.50      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_324,plain,
% 23.29/3.50      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = sK2 ),
% 23.29/3.50      inference(unflattening,[status(thm)],[c_323]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_11,plain,
% 23.29/3.50      ( r1_tarski(X0,X1)
% 23.29/3.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 23.29/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_130,plain,
% 23.29/3.50      ( r1_tarski(X0,X1)
% 23.29/3.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 23.29/3.50      inference(prop_impl,[status(thm)],[c_11]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_17,negated_conjecture,
% 23.29/3.50      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 23.29/3.50      inference(cnf_transformation,[],[f46]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_313,plain,
% 23.29/3.50      ( ~ r1_xboole_0(sK2,sK4)
% 23.29/3.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 23.29/3.50      | sK3 != X1
% 23.29/3.50      | sK2 != X0 ),
% 23.29/3.50      inference(resolution_lifted,[status(thm)],[c_130,c_17]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(c_314,plain,
% 23.29/3.50      ( ~ r1_xboole_0(sK2,sK4)
% 23.29/3.50      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 23.29/3.50      inference(unflattening,[status(thm)],[c_313]) ).
% 23.29/3.50  
% 23.29/3.50  cnf(contradiction,plain,
% 23.29/3.50      ( $false ),
% 23.29/3.50      inference(minisat,
% 23.29/3.50                [status(thm)],
% 23.29/3.50                [c_86244,c_31796,c_14678,c_6349,c_6348,c_5904,c_2592,
% 23.29/3.50                 c_1045,c_943,c_940,c_324,c_314]) ).
% 23.29/3.50  
% 23.29/3.50  
% 23.29/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.29/3.50  
% 23.29/3.50  ------                               Statistics
% 23.29/3.50  
% 23.29/3.50  ------ Selected
% 23.29/3.50  
% 23.29/3.50  total_time:                             2.551
% 23.29/3.50  
%------------------------------------------------------------------------------
