%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:52 EST 2020

% Result     : Timeout 59.61s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  116 ( 721 expanded)
%              Number of clauses        :   66 ( 286 expanded)
%              Number of leaves         :   16 ( 179 expanded)
%              Depth                    :   26
%              Number of atoms          :  241 (1104 expanded)
%              Number of equality atoms :  114 ( 707 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f31])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f47,f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f31])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)
   => k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).

fof(f50,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1049,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_17])).

cnf(c_1430,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_15,c_1049])).

cnf(c_1439,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1430,c_1049])).

cnf(c_1561,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_18,c_1439])).

cnf(c_1576,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1561,c_18])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_743,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_744,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_749,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8626,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_749])).

cnf(c_335343,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_743,c_8626])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_746,plain,
    ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_337935,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_335343,c_746])).

cnf(c_338557,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1576,c_337935])).

cnf(c_1432,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1049,c_15])).

cnf(c_1435,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1432,c_15])).

cnf(c_1500,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1435,c_17])).

cnf(c_14,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_859,plain,
    ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_1052,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_859,c_17])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_196,plain,
    ( X0 != X1
    | k3_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_197,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_945,plain,
    ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_16,c_197])).

cnf(c_1236,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_945,c_18])).

cnf(c_1241,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1236,c_16])).

cnf(c_1346,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1052,c_1241])).

cnf(c_1506,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1500,c_1346])).

cnf(c_1518,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1506])).

cnf(c_1542,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_1518,c_15])).

cnf(c_1544,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1542,c_14])).

cnf(c_1657,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1544])).

cnf(c_2230,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_15,c_1657])).

cnf(c_2283,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2230,c_1657])).

cnf(c_2853,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_18,c_2283])).

cnf(c_988,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_197,c_15])).

cnf(c_993,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_988,c_14])).

cnf(c_2923,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2853,c_993])).

cnf(c_3269,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_18,c_2923])).

cnf(c_341340,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),o_0_0_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_338557,c_3269])).

cnf(c_3295,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2923,c_1049])).

cnf(c_341370,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),o_0_0_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_341340,c_3295])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_748,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2476,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_748])).

cnf(c_1536,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_1518])).

cnf(c_1600,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1536])).

cnf(c_1716,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_993,c_1600])).

cnf(c_1739,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1716,c_18])).

cnf(c_3499,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_749])).

cnf(c_11901,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2476,c_3499])).

cnf(c_11908,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_11901])).

cnf(c_12187,plain,
    ( k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_11908,c_746])).

cnf(c_341371,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_341370,c_14,c_12187])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_342529,plain,
    ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_341371,c_19])).

cnf(c_342580,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_342529])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:26:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 59.61/8.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.61/8.02  
% 59.61/8.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.61/8.02  
% 59.61/8.02  ------  iProver source info
% 59.61/8.02  
% 59.61/8.02  git: date: 2020-06-30 10:37:57 +0100
% 59.61/8.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.61/8.02  git: non_committed_changes: false
% 59.61/8.02  git: last_make_outside_of_git: false
% 59.61/8.02  
% 59.61/8.02  ------ 
% 59.61/8.02  
% 59.61/8.02  ------ Input Options
% 59.61/8.02  
% 59.61/8.02  --out_options                           all
% 59.61/8.02  --tptp_safe_out                         true
% 59.61/8.02  --problem_path                          ""
% 59.61/8.02  --include_path                          ""
% 59.61/8.02  --clausifier                            res/vclausify_rel
% 59.61/8.02  --clausifier_options                    --mode clausify
% 59.61/8.02  --stdin                                 false
% 59.61/8.02  --stats_out                             all
% 59.61/8.02  
% 59.61/8.02  ------ General Options
% 59.61/8.02  
% 59.61/8.02  --fof                                   false
% 59.61/8.02  --time_out_real                         305.
% 59.61/8.02  --time_out_virtual                      -1.
% 59.61/8.02  --symbol_type_check                     false
% 59.61/8.02  --clausify_out                          false
% 59.61/8.02  --sig_cnt_out                           false
% 59.61/8.02  --trig_cnt_out                          false
% 59.61/8.02  --trig_cnt_out_tolerance                1.
% 59.61/8.02  --trig_cnt_out_sk_spl                   false
% 59.61/8.02  --abstr_cl_out                          false
% 59.61/8.02  
% 59.61/8.02  ------ Global Options
% 59.61/8.02  
% 59.61/8.02  --schedule                              default
% 59.61/8.02  --add_important_lit                     false
% 59.61/8.02  --prop_solver_per_cl                    1000
% 59.61/8.02  --min_unsat_core                        false
% 59.61/8.02  --soft_assumptions                      false
% 59.61/8.02  --soft_lemma_size                       3
% 59.61/8.02  --prop_impl_unit_size                   0
% 59.61/8.02  --prop_impl_unit                        []
% 59.61/8.02  --share_sel_clauses                     true
% 59.61/8.02  --reset_solvers                         false
% 59.61/8.02  --bc_imp_inh                            [conj_cone]
% 59.61/8.02  --conj_cone_tolerance                   3.
% 59.61/8.02  --extra_neg_conj                        none
% 59.61/8.02  --large_theory_mode                     true
% 59.61/8.02  --prolific_symb_bound                   200
% 59.61/8.02  --lt_threshold                          2000
% 59.61/8.02  --clause_weak_htbl                      true
% 59.61/8.02  --gc_record_bc_elim                     false
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing Options
% 59.61/8.02  
% 59.61/8.02  --preprocessing_flag                    true
% 59.61/8.02  --time_out_prep_mult                    0.1
% 59.61/8.02  --splitting_mode                        input
% 59.61/8.02  --splitting_grd                         true
% 59.61/8.02  --splitting_cvd                         false
% 59.61/8.02  --splitting_cvd_svl                     false
% 59.61/8.02  --splitting_nvd                         32
% 59.61/8.02  --sub_typing                            true
% 59.61/8.02  --prep_gs_sim                           true
% 59.61/8.02  --prep_unflatten                        true
% 59.61/8.02  --prep_res_sim                          true
% 59.61/8.02  --prep_upred                            true
% 59.61/8.02  --prep_sem_filter                       exhaustive
% 59.61/8.02  --prep_sem_filter_out                   false
% 59.61/8.02  --pred_elim                             true
% 59.61/8.02  --res_sim_input                         true
% 59.61/8.02  --eq_ax_congr_red                       true
% 59.61/8.02  --pure_diseq_elim                       true
% 59.61/8.02  --brand_transform                       false
% 59.61/8.02  --non_eq_to_eq                          false
% 59.61/8.02  --prep_def_merge                        true
% 59.61/8.02  --prep_def_merge_prop_impl              false
% 59.61/8.02  --prep_def_merge_mbd                    true
% 59.61/8.02  --prep_def_merge_tr_red                 false
% 59.61/8.02  --prep_def_merge_tr_cl                  false
% 59.61/8.02  --smt_preprocessing                     true
% 59.61/8.02  --smt_ac_axioms                         fast
% 59.61/8.02  --preprocessed_out                      false
% 59.61/8.02  --preprocessed_stats                    false
% 59.61/8.02  
% 59.61/8.02  ------ Abstraction refinement Options
% 59.61/8.02  
% 59.61/8.02  --abstr_ref                             []
% 59.61/8.02  --abstr_ref_prep                        false
% 59.61/8.02  --abstr_ref_until_sat                   false
% 59.61/8.02  --abstr_ref_sig_restrict                funpre
% 59.61/8.02  --abstr_ref_af_restrict_to_split_sk     false
% 59.61/8.02  --abstr_ref_under                       []
% 59.61/8.02  
% 59.61/8.02  ------ SAT Options
% 59.61/8.02  
% 59.61/8.02  --sat_mode                              false
% 59.61/8.02  --sat_fm_restart_options                ""
% 59.61/8.02  --sat_gr_def                            false
% 59.61/8.02  --sat_epr_types                         true
% 59.61/8.02  --sat_non_cyclic_types                  false
% 59.61/8.02  --sat_finite_models                     false
% 59.61/8.02  --sat_fm_lemmas                         false
% 59.61/8.02  --sat_fm_prep                           false
% 59.61/8.02  --sat_fm_uc_incr                        true
% 59.61/8.02  --sat_out_model                         small
% 59.61/8.02  --sat_out_clauses                       false
% 59.61/8.02  
% 59.61/8.02  ------ QBF Options
% 59.61/8.02  
% 59.61/8.02  --qbf_mode                              false
% 59.61/8.02  --qbf_elim_univ                         false
% 59.61/8.02  --qbf_dom_inst                          none
% 59.61/8.02  --qbf_dom_pre_inst                      false
% 59.61/8.02  --qbf_sk_in                             false
% 59.61/8.02  --qbf_pred_elim                         true
% 59.61/8.02  --qbf_split                             512
% 59.61/8.02  
% 59.61/8.02  ------ BMC1 Options
% 59.61/8.02  
% 59.61/8.02  --bmc1_incremental                      false
% 59.61/8.02  --bmc1_axioms                           reachable_all
% 59.61/8.02  --bmc1_min_bound                        0
% 59.61/8.02  --bmc1_max_bound                        -1
% 59.61/8.02  --bmc1_max_bound_default                -1
% 59.61/8.02  --bmc1_symbol_reachability              true
% 59.61/8.02  --bmc1_property_lemmas                  false
% 59.61/8.02  --bmc1_k_induction                      false
% 59.61/8.02  --bmc1_non_equiv_states                 false
% 59.61/8.02  --bmc1_deadlock                         false
% 59.61/8.02  --bmc1_ucm                              false
% 59.61/8.02  --bmc1_add_unsat_core                   none
% 59.61/8.02  --bmc1_unsat_core_children              false
% 59.61/8.02  --bmc1_unsat_core_extrapolate_axioms    false
% 59.61/8.02  --bmc1_out_stat                         full
% 59.61/8.02  --bmc1_ground_init                      false
% 59.61/8.02  --bmc1_pre_inst_next_state              false
% 59.61/8.02  --bmc1_pre_inst_state                   false
% 59.61/8.02  --bmc1_pre_inst_reach_state             false
% 59.61/8.02  --bmc1_out_unsat_core                   false
% 59.61/8.02  --bmc1_aig_witness_out                  false
% 59.61/8.02  --bmc1_verbose                          false
% 59.61/8.02  --bmc1_dump_clauses_tptp                false
% 59.61/8.02  --bmc1_dump_unsat_core_tptp             false
% 59.61/8.02  --bmc1_dump_file                        -
% 59.61/8.02  --bmc1_ucm_expand_uc_limit              128
% 59.61/8.02  --bmc1_ucm_n_expand_iterations          6
% 59.61/8.02  --bmc1_ucm_extend_mode                  1
% 59.61/8.02  --bmc1_ucm_init_mode                    2
% 59.61/8.02  --bmc1_ucm_cone_mode                    none
% 59.61/8.02  --bmc1_ucm_reduced_relation_type        0
% 59.61/8.02  --bmc1_ucm_relax_model                  4
% 59.61/8.02  --bmc1_ucm_full_tr_after_sat            true
% 59.61/8.02  --bmc1_ucm_expand_neg_assumptions       false
% 59.61/8.02  --bmc1_ucm_layered_model                none
% 59.61/8.02  --bmc1_ucm_max_lemma_size               10
% 59.61/8.02  
% 59.61/8.02  ------ AIG Options
% 59.61/8.02  
% 59.61/8.02  --aig_mode                              false
% 59.61/8.02  
% 59.61/8.02  ------ Instantiation Options
% 59.61/8.02  
% 59.61/8.02  --instantiation_flag                    true
% 59.61/8.02  --inst_sos_flag                         false
% 59.61/8.02  --inst_sos_phase                        true
% 59.61/8.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.61/8.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.61/8.02  --inst_lit_sel_side                     num_symb
% 59.61/8.02  --inst_solver_per_active                1400
% 59.61/8.02  --inst_solver_calls_frac                1.
% 59.61/8.02  --inst_passive_queue_type               priority_queues
% 59.61/8.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.61/8.02  --inst_passive_queues_freq              [25;2]
% 59.61/8.02  --inst_dismatching                      true
% 59.61/8.02  --inst_eager_unprocessed_to_passive     true
% 59.61/8.02  --inst_prop_sim_given                   true
% 59.61/8.02  --inst_prop_sim_new                     false
% 59.61/8.02  --inst_subs_new                         false
% 59.61/8.02  --inst_eq_res_simp                      false
% 59.61/8.02  --inst_subs_given                       false
% 59.61/8.02  --inst_orphan_elimination               true
% 59.61/8.02  --inst_learning_loop_flag               true
% 59.61/8.02  --inst_learning_start                   3000
% 59.61/8.02  --inst_learning_factor                  2
% 59.61/8.02  --inst_start_prop_sim_after_learn       3
% 59.61/8.02  --inst_sel_renew                        solver
% 59.61/8.02  --inst_lit_activity_flag                true
% 59.61/8.02  --inst_restr_to_given                   false
% 59.61/8.02  --inst_activity_threshold               500
% 59.61/8.02  --inst_out_proof                        true
% 59.61/8.02  
% 59.61/8.02  ------ Resolution Options
% 59.61/8.02  
% 59.61/8.02  --resolution_flag                       true
% 59.61/8.02  --res_lit_sel                           adaptive
% 59.61/8.02  --res_lit_sel_side                      none
% 59.61/8.02  --res_ordering                          kbo
% 59.61/8.02  --res_to_prop_solver                    active
% 59.61/8.02  --res_prop_simpl_new                    false
% 59.61/8.02  --res_prop_simpl_given                  true
% 59.61/8.02  --res_passive_queue_type                priority_queues
% 59.61/8.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.61/8.02  --res_passive_queues_freq               [15;5]
% 59.61/8.02  --res_forward_subs                      full
% 59.61/8.02  --res_backward_subs                     full
% 59.61/8.02  --res_forward_subs_resolution           true
% 59.61/8.02  --res_backward_subs_resolution          true
% 59.61/8.02  --res_orphan_elimination                true
% 59.61/8.02  --res_time_limit                        2.
% 59.61/8.02  --res_out_proof                         true
% 59.61/8.02  
% 59.61/8.02  ------ Superposition Options
% 59.61/8.02  
% 59.61/8.02  --superposition_flag                    true
% 59.61/8.02  --sup_passive_queue_type                priority_queues
% 59.61/8.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.61/8.02  --sup_passive_queues_freq               [8;1;4]
% 59.61/8.02  --demod_completeness_check              fast
% 59.61/8.02  --demod_use_ground                      true
% 59.61/8.02  --sup_to_prop_solver                    passive
% 59.61/8.02  --sup_prop_simpl_new                    true
% 59.61/8.02  --sup_prop_simpl_given                  true
% 59.61/8.02  --sup_fun_splitting                     false
% 59.61/8.02  --sup_smt_interval                      50000
% 59.61/8.02  
% 59.61/8.02  ------ Superposition Simplification Setup
% 59.61/8.02  
% 59.61/8.02  --sup_indices_passive                   []
% 59.61/8.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_full_triv                         [TrivRules;PropSubs]
% 59.61/8.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_full_bw                           [BwDemod]
% 59.61/8.02  --sup_immed_triv                        [TrivRules]
% 59.61/8.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.61/8.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_immed_bw_main                     []
% 59.61/8.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.61/8.02  --sup_input_triv                        [Unflattening;TrivRules]
% 59.61/8.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.61/8.02  
% 59.61/8.02  ------ Combination Options
% 59.61/8.02  
% 59.61/8.02  --comb_res_mult                         3
% 59.61/8.02  --comb_sup_mult                         2
% 59.61/8.02  --comb_inst_mult                        10
% 59.61/8.02  
% 59.61/8.02  ------ Debug Options
% 59.61/8.02  
% 59.61/8.02  --dbg_backtrace                         false
% 59.61/8.02  --dbg_dump_prop_clauses                 false
% 59.61/8.02  --dbg_dump_prop_clauses_file            -
% 59.61/8.02  --dbg_out_stat                          false
% 59.61/8.02  ------ Parsing...
% 59.61/8.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.61/8.02  ------ Proving...
% 59.61/8.02  ------ Problem Properties 
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  clauses                                 19
% 59.61/8.02  conjectures                             1
% 59.61/8.02  EPR                                     1
% 59.61/8.02  Horn                                    13
% 59.61/8.02  unary                                   8
% 59.61/8.02  binary                                  6
% 59.61/8.02  lits                                    36
% 59.61/8.02  lits eq                                 13
% 59.61/8.02  fd_pure                                 0
% 59.61/8.02  fd_pseudo                               0
% 59.61/8.02  fd_cond                                 0
% 59.61/8.02  fd_pseudo_cond                          3
% 59.61/8.02  AC symbols                              0
% 59.61/8.02  
% 59.61/8.02  ------ Schedule dynamic 5 is on 
% 59.61/8.02  
% 59.61/8.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  ------ 
% 59.61/8.02  Current options:
% 59.61/8.02  ------ 
% 59.61/8.02  
% 59.61/8.02  ------ Input Options
% 59.61/8.02  
% 59.61/8.02  --out_options                           all
% 59.61/8.02  --tptp_safe_out                         true
% 59.61/8.02  --problem_path                          ""
% 59.61/8.02  --include_path                          ""
% 59.61/8.02  --clausifier                            res/vclausify_rel
% 59.61/8.02  --clausifier_options                    --mode clausify
% 59.61/8.02  --stdin                                 false
% 59.61/8.02  --stats_out                             all
% 59.61/8.02  
% 59.61/8.02  ------ General Options
% 59.61/8.02  
% 59.61/8.02  --fof                                   false
% 59.61/8.02  --time_out_real                         305.
% 59.61/8.02  --time_out_virtual                      -1.
% 59.61/8.02  --symbol_type_check                     false
% 59.61/8.02  --clausify_out                          false
% 59.61/8.02  --sig_cnt_out                           false
% 59.61/8.02  --trig_cnt_out                          false
% 59.61/8.02  --trig_cnt_out_tolerance                1.
% 59.61/8.02  --trig_cnt_out_sk_spl                   false
% 59.61/8.02  --abstr_cl_out                          false
% 59.61/8.02  
% 59.61/8.02  ------ Global Options
% 59.61/8.02  
% 59.61/8.02  --schedule                              default
% 59.61/8.02  --add_important_lit                     false
% 59.61/8.02  --prop_solver_per_cl                    1000
% 59.61/8.02  --min_unsat_core                        false
% 59.61/8.02  --soft_assumptions                      false
% 59.61/8.02  --soft_lemma_size                       3
% 59.61/8.02  --prop_impl_unit_size                   0
% 59.61/8.02  --prop_impl_unit                        []
% 59.61/8.02  --share_sel_clauses                     true
% 59.61/8.02  --reset_solvers                         false
% 59.61/8.02  --bc_imp_inh                            [conj_cone]
% 59.61/8.02  --conj_cone_tolerance                   3.
% 59.61/8.02  --extra_neg_conj                        none
% 59.61/8.02  --large_theory_mode                     true
% 59.61/8.02  --prolific_symb_bound                   200
% 59.61/8.02  --lt_threshold                          2000
% 59.61/8.02  --clause_weak_htbl                      true
% 59.61/8.02  --gc_record_bc_elim                     false
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing Options
% 59.61/8.02  
% 59.61/8.02  --preprocessing_flag                    true
% 59.61/8.02  --time_out_prep_mult                    0.1
% 59.61/8.02  --splitting_mode                        input
% 59.61/8.02  --splitting_grd                         true
% 59.61/8.02  --splitting_cvd                         false
% 59.61/8.02  --splitting_cvd_svl                     false
% 59.61/8.02  --splitting_nvd                         32
% 59.61/8.02  --sub_typing                            true
% 59.61/8.02  --prep_gs_sim                           true
% 59.61/8.02  --prep_unflatten                        true
% 59.61/8.02  --prep_res_sim                          true
% 59.61/8.02  --prep_upred                            true
% 59.61/8.02  --prep_sem_filter                       exhaustive
% 59.61/8.02  --prep_sem_filter_out                   false
% 59.61/8.02  --pred_elim                             true
% 59.61/8.02  --res_sim_input                         true
% 59.61/8.02  --eq_ax_congr_red                       true
% 59.61/8.02  --pure_diseq_elim                       true
% 59.61/8.02  --brand_transform                       false
% 59.61/8.02  --non_eq_to_eq                          false
% 59.61/8.02  --prep_def_merge                        true
% 59.61/8.02  --prep_def_merge_prop_impl              false
% 59.61/8.02  --prep_def_merge_mbd                    true
% 59.61/8.02  --prep_def_merge_tr_red                 false
% 59.61/8.02  --prep_def_merge_tr_cl                  false
% 59.61/8.02  --smt_preprocessing                     true
% 59.61/8.02  --smt_ac_axioms                         fast
% 59.61/8.02  --preprocessed_out                      false
% 59.61/8.02  --preprocessed_stats                    false
% 59.61/8.02  
% 59.61/8.02  ------ Abstraction refinement Options
% 59.61/8.02  
% 59.61/8.02  --abstr_ref                             []
% 59.61/8.02  --abstr_ref_prep                        false
% 59.61/8.02  --abstr_ref_until_sat                   false
% 59.61/8.02  --abstr_ref_sig_restrict                funpre
% 59.61/8.02  --abstr_ref_af_restrict_to_split_sk     false
% 59.61/8.02  --abstr_ref_under                       []
% 59.61/8.02  
% 59.61/8.02  ------ SAT Options
% 59.61/8.02  
% 59.61/8.02  --sat_mode                              false
% 59.61/8.02  --sat_fm_restart_options                ""
% 59.61/8.02  --sat_gr_def                            false
% 59.61/8.02  --sat_epr_types                         true
% 59.61/8.02  --sat_non_cyclic_types                  false
% 59.61/8.02  --sat_finite_models                     false
% 59.61/8.02  --sat_fm_lemmas                         false
% 59.61/8.02  --sat_fm_prep                           false
% 59.61/8.02  --sat_fm_uc_incr                        true
% 59.61/8.02  --sat_out_model                         small
% 59.61/8.02  --sat_out_clauses                       false
% 59.61/8.02  
% 59.61/8.02  ------ QBF Options
% 59.61/8.02  
% 59.61/8.02  --qbf_mode                              false
% 59.61/8.02  --qbf_elim_univ                         false
% 59.61/8.02  --qbf_dom_inst                          none
% 59.61/8.02  --qbf_dom_pre_inst                      false
% 59.61/8.02  --qbf_sk_in                             false
% 59.61/8.02  --qbf_pred_elim                         true
% 59.61/8.02  --qbf_split                             512
% 59.61/8.02  
% 59.61/8.02  ------ BMC1 Options
% 59.61/8.02  
% 59.61/8.02  --bmc1_incremental                      false
% 59.61/8.02  --bmc1_axioms                           reachable_all
% 59.61/8.02  --bmc1_min_bound                        0
% 59.61/8.02  --bmc1_max_bound                        -1
% 59.61/8.02  --bmc1_max_bound_default                -1
% 59.61/8.02  --bmc1_symbol_reachability              true
% 59.61/8.02  --bmc1_property_lemmas                  false
% 59.61/8.02  --bmc1_k_induction                      false
% 59.61/8.02  --bmc1_non_equiv_states                 false
% 59.61/8.02  --bmc1_deadlock                         false
% 59.61/8.02  --bmc1_ucm                              false
% 59.61/8.02  --bmc1_add_unsat_core                   none
% 59.61/8.02  --bmc1_unsat_core_children              false
% 59.61/8.02  --bmc1_unsat_core_extrapolate_axioms    false
% 59.61/8.02  --bmc1_out_stat                         full
% 59.61/8.02  --bmc1_ground_init                      false
% 59.61/8.02  --bmc1_pre_inst_next_state              false
% 59.61/8.02  --bmc1_pre_inst_state                   false
% 59.61/8.02  --bmc1_pre_inst_reach_state             false
% 59.61/8.02  --bmc1_out_unsat_core                   false
% 59.61/8.02  --bmc1_aig_witness_out                  false
% 59.61/8.02  --bmc1_verbose                          false
% 59.61/8.02  --bmc1_dump_clauses_tptp                false
% 59.61/8.02  --bmc1_dump_unsat_core_tptp             false
% 59.61/8.02  --bmc1_dump_file                        -
% 59.61/8.02  --bmc1_ucm_expand_uc_limit              128
% 59.61/8.02  --bmc1_ucm_n_expand_iterations          6
% 59.61/8.02  --bmc1_ucm_extend_mode                  1
% 59.61/8.02  --bmc1_ucm_init_mode                    2
% 59.61/8.02  --bmc1_ucm_cone_mode                    none
% 59.61/8.02  --bmc1_ucm_reduced_relation_type        0
% 59.61/8.02  --bmc1_ucm_relax_model                  4
% 59.61/8.02  --bmc1_ucm_full_tr_after_sat            true
% 59.61/8.02  --bmc1_ucm_expand_neg_assumptions       false
% 59.61/8.02  --bmc1_ucm_layered_model                none
% 59.61/8.02  --bmc1_ucm_max_lemma_size               10
% 59.61/8.02  
% 59.61/8.02  ------ AIG Options
% 59.61/8.02  
% 59.61/8.02  --aig_mode                              false
% 59.61/8.02  
% 59.61/8.02  ------ Instantiation Options
% 59.61/8.02  
% 59.61/8.02  --instantiation_flag                    true
% 59.61/8.02  --inst_sos_flag                         false
% 59.61/8.02  --inst_sos_phase                        true
% 59.61/8.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.61/8.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.61/8.02  --inst_lit_sel_side                     none
% 59.61/8.02  --inst_solver_per_active                1400
% 59.61/8.02  --inst_solver_calls_frac                1.
% 59.61/8.02  --inst_passive_queue_type               priority_queues
% 59.61/8.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.61/8.02  --inst_passive_queues_freq              [25;2]
% 59.61/8.02  --inst_dismatching                      true
% 59.61/8.02  --inst_eager_unprocessed_to_passive     true
% 59.61/8.02  --inst_prop_sim_given                   true
% 59.61/8.02  --inst_prop_sim_new                     false
% 59.61/8.02  --inst_subs_new                         false
% 59.61/8.02  --inst_eq_res_simp                      false
% 59.61/8.02  --inst_subs_given                       false
% 59.61/8.02  --inst_orphan_elimination               true
% 59.61/8.02  --inst_learning_loop_flag               true
% 59.61/8.02  --inst_learning_start                   3000
% 59.61/8.02  --inst_learning_factor                  2
% 59.61/8.02  --inst_start_prop_sim_after_learn       3
% 59.61/8.02  --inst_sel_renew                        solver
% 59.61/8.02  --inst_lit_activity_flag                true
% 59.61/8.02  --inst_restr_to_given                   false
% 59.61/8.02  --inst_activity_threshold               500
% 59.61/8.02  --inst_out_proof                        true
% 59.61/8.02  
% 59.61/8.02  ------ Resolution Options
% 59.61/8.02  
% 59.61/8.02  --resolution_flag                       false
% 59.61/8.02  --res_lit_sel                           adaptive
% 59.61/8.02  --res_lit_sel_side                      none
% 59.61/8.02  --res_ordering                          kbo
% 59.61/8.02  --res_to_prop_solver                    active
% 59.61/8.02  --res_prop_simpl_new                    false
% 59.61/8.02  --res_prop_simpl_given                  true
% 59.61/8.02  --res_passive_queue_type                priority_queues
% 59.61/8.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.61/8.02  --res_passive_queues_freq               [15;5]
% 59.61/8.02  --res_forward_subs                      full
% 59.61/8.02  --res_backward_subs                     full
% 59.61/8.02  --res_forward_subs_resolution           true
% 59.61/8.02  --res_backward_subs_resolution          true
% 59.61/8.02  --res_orphan_elimination                true
% 59.61/8.02  --res_time_limit                        2.
% 59.61/8.02  --res_out_proof                         true
% 59.61/8.02  
% 59.61/8.02  ------ Superposition Options
% 59.61/8.02  
% 59.61/8.02  --superposition_flag                    true
% 59.61/8.02  --sup_passive_queue_type                priority_queues
% 59.61/8.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.61/8.02  --sup_passive_queues_freq               [8;1;4]
% 59.61/8.02  --demod_completeness_check              fast
% 59.61/8.02  --demod_use_ground                      true
% 59.61/8.02  --sup_to_prop_solver                    passive
% 59.61/8.02  --sup_prop_simpl_new                    true
% 59.61/8.02  --sup_prop_simpl_given                  true
% 59.61/8.02  --sup_fun_splitting                     false
% 59.61/8.02  --sup_smt_interval                      50000
% 59.61/8.02  
% 59.61/8.02  ------ Superposition Simplification Setup
% 59.61/8.02  
% 59.61/8.02  --sup_indices_passive                   []
% 59.61/8.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 59.61/8.02  --sup_full_triv                         [TrivRules;PropSubs]
% 59.61/8.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_full_bw                           [BwDemod]
% 59.61/8.02  --sup_immed_triv                        [TrivRules]
% 59.61/8.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.61/8.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_immed_bw_main                     []
% 59.61/8.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.61/8.02  --sup_input_triv                        [Unflattening;TrivRules]
% 59.61/8.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 59.61/8.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 59.61/8.02  
% 59.61/8.02  ------ Combination Options
% 59.61/8.02  
% 59.61/8.02  --comb_res_mult                         3
% 59.61/8.02  --comb_sup_mult                         2
% 59.61/8.02  --comb_inst_mult                        10
% 59.61/8.02  
% 59.61/8.02  ------ Debug Options
% 59.61/8.02  
% 59.61/8.02  --dbg_backtrace                         false
% 59.61/8.02  --dbg_dump_prop_clauses                 false
% 59.61/8.02  --dbg_dump_prop_clauses_file            -
% 59.61/8.02  --dbg_out_stat                          false
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  ------ Proving...
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  % SZS status Theorem for theBenchmark.p
% 59.61/8.02  
% 59.61/8.02   Resolution empty clause
% 59.61/8.02  
% 59.61/8.02  % SZS output start CNFRefutation for theBenchmark.p
% 59.61/8.02  
% 59.61/8.02  fof(f12,axiom,(
% 59.61/8.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f49,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 59.61/8.02    inference(cnf_transformation,[],[f12])).
% 59.61/8.02  
% 59.61/8.02  fof(f9,axiom,(
% 59.61/8.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f46,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 59.61/8.02    inference(cnf_transformation,[],[f9])).
% 59.61/8.02  
% 59.61/8.02  fof(f1,axiom,(
% 59.61/8.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f30,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f1])).
% 59.61/8.02  
% 59.61/8.02  fof(f11,axiom,(
% 59.61/8.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f48,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f11])).
% 59.61/8.02  
% 59.61/8.02  fof(f5,axiom,(
% 59.61/8.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f15,plain,(
% 59.61/8.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 59.61/8.02    inference(rectify,[],[f5])).
% 59.61/8.02  
% 59.61/8.02  fof(f17,plain,(
% 59.61/8.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 59.61/8.02    inference(ennf_transformation,[],[f15])).
% 59.61/8.02  
% 59.61/8.02  fof(f26,plain,(
% 59.61/8.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 59.61/8.02    introduced(choice_axiom,[])).
% 59.61/8.02  
% 59.61/8.02  fof(f27,plain,(
% 59.61/8.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 59.61/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f26])).
% 59.61/8.02  
% 59.61/8.02  fof(f40,plain,(
% 59.61/8.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f27])).
% 59.61/8.02  
% 59.61/8.02  fof(f41,plain,(
% 59.61/8.02    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f27])).
% 59.61/8.02  
% 59.61/8.02  fof(f3,axiom,(
% 59.61/8.02    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f20,plain,(
% 59.61/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.61/8.02    inference(nnf_transformation,[],[f3])).
% 59.61/8.02  
% 59.61/8.02  fof(f21,plain,(
% 59.61/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.61/8.02    inference(flattening,[],[f20])).
% 59.61/8.02  
% 59.61/8.02  fof(f22,plain,(
% 59.61/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.61/8.02    inference(rectify,[],[f21])).
% 59.61/8.02  
% 59.61/8.02  fof(f23,plain,(
% 59.61/8.02    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 59.61/8.02    introduced(choice_axiom,[])).
% 59.61/8.02  
% 59.61/8.02  fof(f24,plain,(
% 59.61/8.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 59.61/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 59.61/8.02  
% 59.61/8.02  fof(f33,plain,(
% 59.61/8.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 59.61/8.02    inference(cnf_transformation,[],[f24])).
% 59.61/8.02  
% 59.61/8.02  fof(f57,plain,(
% 59.61/8.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 59.61/8.02    inference(equality_resolution,[],[f33])).
% 59.61/8.02  
% 59.61/8.02  fof(f4,axiom,(
% 59.61/8.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k1_xboole_0 = k3_xboole_0(X0,X1))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f25,plain,(
% 59.61/8.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k1_xboole_0 != k3_xboole_0(X0,X1)) & (k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)))),
% 59.61/8.02    inference(nnf_transformation,[],[f4])).
% 59.61/8.02  
% 59.61/8.02  fof(f38,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f25])).
% 59.61/8.02  
% 59.61/8.02  fof(f2,axiom,(
% 59.61/8.02    k1_xboole_0 = o_0_0_xboole_0),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f31,plain,(
% 59.61/8.02    k1_xboole_0 = o_0_0_xboole_0),
% 59.61/8.02    inference(cnf_transformation,[],[f2])).
% 59.61/8.02  
% 59.61/8.02  fof(f52,plain,(
% 59.61/8.02    ( ! [X0,X1] : (o_0_0_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 59.61/8.02    inference(definition_unfolding,[],[f38,f31])).
% 59.61/8.02  
% 59.61/8.02  fof(f8,axiom,(
% 59.61/8.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f45,plain,(
% 59.61/8.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.61/8.02    inference(cnf_transformation,[],[f8])).
% 59.61/8.02  
% 59.61/8.02  fof(f54,plain,(
% 59.61/8.02    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 59.61/8.02    inference(definition_unfolding,[],[f45,f31])).
% 59.61/8.02  
% 59.61/8.02  fof(f10,axiom,(
% 59.61/8.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f47,plain,(
% 59.61/8.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.61/8.02    inference(cnf_transformation,[],[f10])).
% 59.61/8.02  
% 59.61/8.02  fof(f55,plain,(
% 59.61/8.02    ( ! [X0] : (k4_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 59.61/8.02    inference(definition_unfolding,[],[f47,f31])).
% 59.61/8.02  
% 59.61/8.02  fof(f6,axiom,(
% 59.61/8.02    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f16,plain,(
% 59.61/8.02    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 59.61/8.02    inference(unused_predicate_definition_removal,[],[f6])).
% 59.61/8.02  
% 59.61/8.02  fof(f18,plain,(
% 59.61/8.02    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 59.61/8.02    inference(ennf_transformation,[],[f16])).
% 59.61/8.02  
% 59.61/8.02  fof(f43,plain,(
% 59.61/8.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f18])).
% 59.61/8.02  
% 59.61/8.02  fof(f53,plain,(
% 59.61/8.02    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 59.61/8.02    inference(definition_unfolding,[],[f43,f31])).
% 59.61/8.02  
% 59.61/8.02  fof(f7,axiom,(
% 59.61/8.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f44,plain,(
% 59.61/8.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 59.61/8.02    inference(cnf_transformation,[],[f7])).
% 59.61/8.02  
% 59.61/8.02  fof(f32,plain,(
% 59.61/8.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 59.61/8.02    inference(cnf_transformation,[],[f24])).
% 59.61/8.02  
% 59.61/8.02  fof(f58,plain,(
% 59.61/8.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 59.61/8.02    inference(equality_resolution,[],[f32])).
% 59.61/8.02  
% 59.61/8.02  fof(f13,conjecture,(
% 59.61/8.02    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 59.61/8.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.61/8.02  
% 59.61/8.02  fof(f14,negated_conjecture,(
% 59.61/8.02    ~! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 59.61/8.02    inference(negated_conjecture,[],[f13])).
% 59.61/8.02  
% 59.61/8.02  fof(f19,plain,(
% 59.61/8.02    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1)),
% 59.61/8.02    inference(ennf_transformation,[],[f14])).
% 59.61/8.02  
% 59.61/8.02  fof(f28,plain,(
% 59.61/8.02    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) => k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3)),
% 59.61/8.02    introduced(choice_axiom,[])).
% 59.61/8.02  
% 59.61/8.02  fof(f29,plain,(
% 59.61/8.02    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3)),
% 59.61/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).
% 59.61/8.02  
% 59.61/8.02  fof(f50,plain,(
% 59.61/8.02    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3)),
% 59.61/8.02    inference(cnf_transformation,[],[f29])).
% 59.61/8.02  
% 59.61/8.02  cnf(c_18,plain,
% 59.61/8.02      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 59.61/8.02      inference(cnf_transformation,[],[f49]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_15,plain,
% 59.61/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.61/8.02      inference(cnf_transformation,[],[f46]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_0,plain,
% 59.61/8.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 59.61/8.02      inference(cnf_transformation,[],[f30]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_17,plain,
% 59.61/8.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 59.61/8.02      inference(cnf_transformation,[],[f48]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1049,plain,
% 59.61/8.02      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_0,c_17]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1430,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_15,c_1049]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1439,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_1430,c_1049]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1561,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_18,c_1439]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1576,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_1561,c_18]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_11,plain,
% 59.61/8.02      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 59.61/8.02      inference(cnf_transformation,[],[f40]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_743,plain,
% 59.61/8.02      ( r1_xboole_0(X0,X1) = iProver_top
% 59.61/8.02      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 59.61/8.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_10,plain,
% 59.61/8.02      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 59.61/8.02      inference(cnf_transformation,[],[f41]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_744,plain,
% 59.61/8.02      ( r1_xboole_0(X0,X1) = iProver_top
% 59.61/8.02      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 59.61/8.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_5,plain,
% 59.61/8.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 59.61/8.02      inference(cnf_transformation,[],[f57]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_749,plain,
% 59.61/8.02      ( r2_hidden(X0,X1) != iProver_top
% 59.61/8.02      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 59.61/8.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_8626,plain,
% 59.61/8.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 59.61/8.02      | r2_hidden(sK1(X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_744,c_749]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_335343,plain,
% 59.61/8.02      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_743,c_8626]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_8,plain,
% 59.61/8.02      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(cnf_transformation,[],[f52]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_746,plain,
% 59.61/8.02      ( k3_xboole_0(X0,X1) = o_0_0_xboole_0
% 59.61/8.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 59.61/8.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_337935,plain,
% 59.61/8.02      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_335343,c_746]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_338557,plain,
% 59.61/8.02      ( k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1576,c_337935]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1432,plain,
% 59.61/8.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1049,c_15]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1435,plain,
% 59.61/8.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_1432,c_15]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1500,plain,
% 59.61/8.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1435,c_17]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_14,plain,
% 59.61/8.02      ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 59.61/8.02      inference(cnf_transformation,[],[f54]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_859,plain,
% 59.61/8.02      ( k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1052,plain,
% 59.61/8.02      ( k4_xboole_0(X0,X0) = k4_xboole_0(o_0_0_xboole_0,X0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_859,c_17]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_16,plain,
% 59.61/8.02      ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 59.61/8.02      inference(cnf_transformation,[],[f55]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_12,plain,
% 59.61/8.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(cnf_transformation,[],[f53]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_13,plain,
% 59.61/8.02      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 59.61/8.02      inference(cnf_transformation,[],[f44]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_196,plain,
% 59.61/8.02      ( X0 != X1
% 59.61/8.02      | k3_xboole_0(X0,X2) != X3
% 59.61/8.02      | k4_xboole_0(X3,X1) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_197,plain,
% 59.61/8.02      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(unflattening,[status(thm)],[c_196]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_945,plain,
% 59.61/8.02      ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_16,c_197]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1236,plain,
% 59.61/8.02      ( k4_xboole_0(o_0_0_xboole_0,X0) = k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_945,c_18]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1241,plain,
% 59.61/8.02      ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_1236,c_16]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1346,plain,
% 59.61/8.02      ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_1052,c_1241]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1506,plain,
% 59.61/8.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_1500,c_1346]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1518,plain,
% 59.61/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_0,c_1506]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1542,plain,
% 59.61/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),o_0_0_xboole_0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1518,c_15]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1544,plain,
% 59.61/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_1542,c_14]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1657,plain,
% 59.61/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_0,c_1544]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_2230,plain,
% 59.61/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_15,c_1657]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_2283,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_2230,c_1657]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_2853,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_18,c_2283]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_988,plain,
% 59.61/8.02      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(X0,o_0_0_xboole_0) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_197,c_15]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_993,plain,
% 59.61/8.02      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_988,c_14]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_2923,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_2853,c_993]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_3269,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_18,c_2923]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_341340,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),o_0_0_xboole_0)) = k3_xboole_0(X0,X1) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_338557,c_3269]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_3295,plain,
% 59.61/8.02      ( k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_2923,c_1049]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_341370,plain,
% 59.61/8.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),o_0_0_xboole_0)) = k3_xboole_0(X0,X1) ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_341340,c_3295]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_6,plain,
% 59.61/8.02      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 59.61/8.02      inference(cnf_transformation,[],[f58]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_748,plain,
% 59.61/8.02      ( r2_hidden(X0,X1) = iProver_top
% 59.61/8.02      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 59.61/8.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_2476,plain,
% 59.61/8.02      ( r2_hidden(X0,X1) = iProver_top
% 59.61/8.02      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1518,c_748]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1536,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_15,c_1518]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1600,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_0,c_1536]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1716,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_993,c_1600]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_1739,plain,
% 59.61/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(light_normalisation,[status(thm)],[c_1716,c_18]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_3499,plain,
% 59.61/8.02      ( r2_hidden(X0,X1) != iProver_top
% 59.61/8.02      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_1739,c_749]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_11901,plain,
% 59.61/8.02      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 59.61/8.02      inference(global_propositional_subsumption,[status(thm)],[c_2476,c_3499]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_11908,plain,
% 59.61/8.02      ( r1_xboole_0(X0,o_0_0_xboole_0) = iProver_top ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_744,c_11901]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_12187,plain,
% 59.61/8.02      ( k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 59.61/8.02      inference(superposition,[status(thm)],[c_11908,c_746]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_341371,plain,
% 59.61/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_341370,c_14,c_12187]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_19,negated_conjecture,
% 59.61/8.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k3_xboole_0(sK2,sK3) ),
% 59.61/8.02      inference(cnf_transformation,[],[f50]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_342529,plain,
% 59.61/8.02      ( k3_xboole_0(sK2,sK3) != k3_xboole_0(sK2,sK3) ),
% 59.61/8.02      inference(demodulation,[status(thm)],[c_341371,c_19]) ).
% 59.61/8.02  
% 59.61/8.02  cnf(c_342580,plain,
% 59.61/8.02      ( $false ),
% 59.61/8.02      inference(equality_resolution_simp,[status(thm)],[c_342529]) ).
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  % SZS output end CNFRefutation for theBenchmark.p
% 59.61/8.02  
% 59.61/8.02  ------                               Statistics
% 59.61/8.02  
% 59.61/8.02  ------ General
% 59.61/8.02  
% 59.61/8.02  abstr_ref_over_cycles:                  0
% 59.61/8.02  abstr_ref_under_cycles:                 0
% 59.61/8.02  gc_basic_clause_elim:                   0
% 59.61/8.02  forced_gc_time:                         0
% 59.61/8.02  parsing_time:                           0.008
% 59.61/8.02  unif_index_cands_time:                  0.
% 59.61/8.02  unif_index_add_time:                    0.
% 59.61/8.02  orderings_time:                         0.
% 59.61/8.02  out_proof_time:                         0.009
% 59.61/8.02  total_time:                             7.364
% 59.61/8.02  num_of_symbols:                         42
% 59.61/8.02  num_of_terms:                           352131
% 59.61/8.02  
% 59.61/8.02  ------ Preprocessing
% 59.61/8.02  
% 59.61/8.02  num_of_splits:                          0
% 59.61/8.02  num_of_split_atoms:                     0
% 59.61/8.02  num_of_reused_defs:                     0
% 59.61/8.02  num_eq_ax_congr_red:                    25
% 59.61/8.02  num_of_sem_filtered_clauses:            1
% 59.61/8.02  num_of_subtypes:                        0
% 59.61/8.02  monotx_restored_types:                  0
% 59.61/8.02  sat_num_of_epr_types:                   0
% 59.61/8.02  sat_num_of_non_cyclic_types:            0
% 59.61/8.02  sat_guarded_non_collapsed_types:        0
% 59.61/8.02  num_pure_diseq_elim:                    0
% 59.61/8.02  simp_replaced_by:                       0
% 59.61/8.02  res_preprocessed:                       90
% 59.61/8.02  prep_upred:                             0
% 59.61/8.02  prep_unflattend:                        2
% 59.61/8.02  smt_new_axioms:                         0
% 59.61/8.02  pred_elim_cands:                        2
% 59.61/8.02  pred_elim:                              1
% 59.61/8.02  pred_elim_cl:                           1
% 59.61/8.02  pred_elim_cycles:                       3
% 59.61/8.02  merged_defs:                            8
% 59.61/8.02  merged_defs_ncl:                        0
% 59.61/8.02  bin_hyper_res:                          8
% 59.61/8.02  prep_cycles:                            4
% 59.61/8.02  pred_elim_time:                         0.002
% 59.61/8.02  splitting_time:                         0.
% 59.61/8.02  sem_filter_time:                        0.
% 59.61/8.02  monotx_time:                            0.
% 59.61/8.02  subtype_inf_time:                       0.
% 59.61/8.02  
% 59.61/8.02  ------ Problem properties
% 59.61/8.02  
% 59.61/8.02  clauses:                                19
% 59.61/8.02  conjectures:                            1
% 59.61/8.02  epr:                                    1
% 59.61/8.02  horn:                                   13
% 59.61/8.02  ground:                                 1
% 59.61/8.02  unary:                                  8
% 59.61/8.02  binary:                                 6
% 59.61/8.02  lits:                                   36
% 59.61/8.02  lits_eq:                                13
% 59.61/8.02  fd_pure:                                0
% 59.61/8.02  fd_pseudo:                              0
% 59.61/8.02  fd_cond:                                0
% 59.61/8.02  fd_pseudo_cond:                         3
% 59.61/8.02  ac_symbols:                             0
% 59.61/8.02  
% 59.61/8.02  ------ Propositional Solver
% 59.61/8.02  
% 59.61/8.02  prop_solver_calls:                      38
% 59.61/8.02  prop_fast_solver_calls:                 1064
% 59.61/8.02  smt_solver_calls:                       0
% 59.61/8.02  smt_fast_solver_calls:                  0
% 59.61/8.02  prop_num_of_clauses:                    37474
% 59.61/8.02  prop_preprocess_simplified:             40874
% 59.61/8.02  prop_fo_subsumed:                       4
% 59.61/8.02  prop_solver_time:                       0.
% 59.61/8.02  smt_solver_time:                        0.
% 59.61/8.02  smt_fast_solver_time:                   0.
% 59.61/8.02  prop_fast_solver_time:                  0.
% 59.61/8.02  prop_unsat_core_time:                   0.
% 59.61/8.02  
% 59.61/8.02  ------ QBF
% 59.61/8.02  
% 59.61/8.02  qbf_q_res:                              0
% 59.61/8.02  qbf_num_tautologies:                    0
% 59.61/8.02  qbf_prep_cycles:                        0
% 59.61/8.02  
% 59.61/8.02  ------ BMC1
% 59.61/8.02  
% 59.61/8.02  bmc1_current_bound:                     -1
% 59.61/8.02  bmc1_last_solved_bound:                 -1
% 59.61/8.02  bmc1_unsat_core_size:                   -1
% 59.61/8.02  bmc1_unsat_core_parents_size:           -1
% 59.61/8.02  bmc1_merge_next_fun:                    0
% 59.61/8.02  bmc1_unsat_core_clauses_time:           0.
% 59.61/8.02  
% 59.61/8.02  ------ Instantiation
% 59.61/8.02  
% 59.61/8.02  inst_num_of_clauses:                    6553
% 59.61/8.02  inst_num_in_passive:                    1979
% 59.61/8.02  inst_num_in_active:                     1568
% 59.61/8.02  inst_num_in_unprocessed:                3006
% 59.61/8.02  inst_num_of_loops:                      2010
% 59.61/8.02  inst_num_of_learning_restarts:          0
% 59.61/8.02  inst_num_moves_active_passive:          436
% 59.61/8.02  inst_lit_activity:                      0
% 59.61/8.02  inst_lit_activity_moves:                1
% 59.61/8.02  inst_num_tautologies:                   0
% 59.61/8.02  inst_num_prop_implied:                  0
% 59.61/8.02  inst_num_existing_simplified:           0
% 59.61/8.02  inst_num_eq_res_simplified:             0
% 59.61/8.02  inst_num_child_elim:                    0
% 59.61/8.02  inst_num_of_dismatching_blockings:      5448
% 59.61/8.02  inst_num_of_non_proper_insts:           7189
% 59.61/8.02  inst_num_of_duplicates:                 0
% 59.61/8.02  inst_inst_num_from_inst_to_res:         0
% 59.61/8.02  inst_dismatching_checking_time:         0.
% 59.61/8.02  
% 59.61/8.02  ------ Resolution
% 59.61/8.02  
% 59.61/8.02  res_num_of_clauses:                     0
% 59.61/8.02  res_num_in_passive:                     0
% 59.61/8.02  res_num_in_active:                      0
% 59.61/8.02  res_num_of_loops:                       94
% 59.61/8.02  res_forward_subset_subsumed:            384
% 59.61/8.02  res_backward_subset_subsumed:           2
% 59.61/8.02  res_forward_subsumed:                   0
% 59.61/8.02  res_backward_subsumed:                  0
% 59.61/8.02  res_forward_subsumption_resolution:     0
% 59.61/8.02  res_backward_subsumption_resolution:    0
% 59.61/8.02  res_clause_to_clause_subsumption:       435673
% 59.61/8.02  res_orphan_elimination:                 0
% 59.61/8.02  res_tautology_del:                      357
% 59.61/8.02  res_num_eq_res_simplified:              0
% 59.61/8.02  res_num_sel_changes:                    0
% 59.61/8.02  res_moves_from_active_to_pass:          0
% 59.61/8.02  
% 59.61/8.02  ------ Superposition
% 59.61/8.02  
% 59.61/8.02  sup_time_total:                         0.
% 59.61/8.02  sup_time_generating:                    0.
% 59.61/8.02  sup_time_sim_full:                      0.
% 59.61/8.02  sup_time_sim_immed:                     0.
% 59.61/8.02  
% 59.61/8.02  sup_num_of_clauses:                     11002
% 59.61/8.02  sup_num_in_active:                      256
% 59.61/8.02  sup_num_in_passive:                     10746
% 59.61/8.02  sup_num_of_loops:                       401
% 59.61/8.02  sup_fw_superposition:                   67133
% 59.61/8.02  sup_bw_superposition:                   41468
% 59.61/8.02  sup_immediate_simplified:               79178
% 59.61/8.02  sup_given_eliminated:                   2
% 59.61/8.02  comparisons_done:                       0
% 59.61/8.02  comparisons_avoided:                    0
% 59.61/8.02  
% 59.61/8.02  ------ Simplifications
% 59.61/8.02  
% 59.61/8.02  
% 59.61/8.02  sim_fw_subset_subsumed:                 353
% 59.61/8.02  sim_bw_subset_subsumed:                 15
% 59.61/8.02  sim_fw_subsumed:                        8690
% 59.61/8.02  sim_bw_subsumed:                        18
% 59.61/8.02  sim_fw_subsumption_res:                 3
% 59.61/8.02  sim_bw_subsumption_res:                 0
% 59.61/8.02  sim_tautology_del:                      286
% 59.61/8.02  sim_eq_tautology_del:                   23021
% 59.61/8.02  sim_eq_res_simp:                        11
% 59.61/8.02  sim_fw_demodulated:                     37889
% 59.61/8.02  sim_bw_demodulated:                     1646
% 59.61/8.02  sim_light_normalised:                   53812
% 59.61/8.02  sim_joinable_taut:                      0
% 59.61/8.02  sim_joinable_simp:                      0
% 59.61/8.02  sim_ac_normalised:                      0
% 59.61/8.02  sim_smt_subsumption:                    0
% 59.61/8.02  
%------------------------------------------------------------------------------
