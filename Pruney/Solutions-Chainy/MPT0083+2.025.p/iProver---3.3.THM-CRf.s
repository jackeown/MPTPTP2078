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
% DateTime   : Thu Dec  3 11:24:12 EST 2020

% Result     : Theorem 27.15s
% Output     : CNFRefutation 27.15s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 237 expanded)
%              Number of clauses        :   58 ( 104 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 491 expanded)
%              Number of equality atoms :   74 ( 155 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4))
      & r1_xboole_0(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4))
    & r1_xboole_0(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f30])).

fof(f47,plain,(
    r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(rectify,[],[f1])).

fof(f18,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_342,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_348,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_350,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5606,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_348,c_350])).

cnf(c_79983,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_342,c_5606])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_347,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_346,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1528,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_347,c_346])).

cnf(c_12,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1808,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_12])).

cnf(c_6,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2035,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1808,c_6])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3882,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2035,c_11])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3895,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3882,c_10])).

cnf(c_12319,plain,
    ( k4_xboole_0(X0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(X2,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_3895,c_3895])).

cnf(c_80346,plain,
    ( k4_xboole_0(sK4,k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_79983,c_12319])).

cnf(c_80361,plain,
    ( k4_xboole_0(sK4,k3_xboole_0(X0,sK3)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_80346,c_10])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_344,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2027,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top
    | r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_344])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_351,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_80318,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_79983,c_350])).

cnf(c_1807,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1528,c_10])).

cnf(c_5609,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_350])).

cnf(c_123,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_122,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2322,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_123,c_122])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4189,plain,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2322,c_8])).

cnf(c_124,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1872,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_124,c_122])).

cnf(c_10412,plain,
    ( ~ r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_4189,c_1872])).

cnf(c_10427,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) != iProver_top
    | r1_xboole_0(k1_xboole_0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10412])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1223,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_3956,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1)
    | r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_1223,c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10949,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_3956,c_1])).

cnf(c_1893,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)
    | ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[status(thm)],[c_1872,c_8])).

cnf(c_10954,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10949,c_1893])).

cnf(c_10967,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10954])).

cnf(c_80562,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_80318,c_5609,c_10427,c_10967])).

cnf(c_80568,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_351,c_80562])).

cnf(c_95592,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2027,c_80568])).

cnf(c_95598,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_95592])).

cnf(c_97890,plain,
    ( r1_xboole_0(k3_xboole_0(X0,sK3),k3_xboole_0(X1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_80361,c_95598])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_343,plain,
    ( r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_137470,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_97890,c_343])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.15/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.15/4.00  
% 27.15/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.15/4.00  
% 27.15/4.00  ------  iProver source info
% 27.15/4.00  
% 27.15/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.15/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.15/4.00  git: non_committed_changes: false
% 27.15/4.00  git: last_make_outside_of_git: false
% 27.15/4.00  
% 27.15/4.00  ------ 
% 27.15/4.00  ------ Parsing...
% 27.15/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.15/4.00  
% 27.15/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.15/4.00  
% 27.15/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.15/4.00  
% 27.15/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.15/4.00  ------ Proving...
% 27.15/4.00  ------ Problem Properties 
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  clauses                                 17
% 27.15/4.00  conjectures                             2
% 27.15/4.00  EPR                                     3
% 27.15/4.00  Horn                                    13
% 27.15/4.00  unary                                   9
% 27.15/4.00  binary                                  7
% 27.15/4.00  lits                                    26
% 27.15/4.00  lits eq                                 7
% 27.15/4.00  fd_pure                                 0
% 27.15/4.00  fd_pseudo                               0
% 27.15/4.00  fd_cond                                 1
% 27.15/4.00  fd_pseudo_cond                          0
% 27.15/4.00  AC symbols                              0
% 27.15/4.00  
% 27.15/4.00  ------ Input Options Time Limit: Unbounded
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  ------ 
% 27.15/4.00  Current options:
% 27.15/4.00  ------ 
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  ------ Proving...
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  % SZS status Theorem for theBenchmark.p
% 27.15/4.00  
% 27.15/4.00   Resolution empty clause
% 27.15/4.00  
% 27.15/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.15/4.00  
% 27.15/4.00  fof(f13,conjecture,(
% 27.15/4.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f14,negated_conjecture,(
% 27.15/4.00    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 27.15/4.00    inference(negated_conjecture,[],[f13])).
% 27.15/4.00  
% 27.15/4.00  fof(f23,plain,(
% 27.15/4.00    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 27.15/4.00    inference(ennf_transformation,[],[f14])).
% 27.15/4.00  
% 27.15/4.00  fof(f30,plain,(
% 27.15/4.00    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) & r1_xboole_0(sK3,sK4))),
% 27.15/4.00    introduced(choice_axiom,[])).
% 27.15/4.00  
% 27.15/4.00  fof(f31,plain,(
% 27.15/4.00    ~r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) & r1_xboole_0(sK3,sK4)),
% 27.15/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f30])).
% 27.15/4.00  
% 27.15/4.00  fof(f47,plain,(
% 27.15/4.00    r1_xboole_0(sK3,sK4)),
% 27.15/4.00    inference(cnf_transformation,[],[f31])).
% 27.15/4.00  
% 27.15/4.00  fof(f3,axiom,(
% 27.15/4.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f20,plain,(
% 27.15/4.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 27.15/4.00    inference(ennf_transformation,[],[f3])).
% 27.15/4.00  
% 27.15/4.00  fof(f28,plain,(
% 27.15/4.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 27.15/4.00    introduced(choice_axiom,[])).
% 27.15/4.00  
% 27.15/4.00  fof(f29,plain,(
% 27.15/4.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 27.15/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).
% 27.15/4.00  
% 27.15/4.00  fof(f37,plain,(
% 27.15/4.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 27.15/4.00    inference(cnf_transformation,[],[f29])).
% 27.15/4.00  
% 27.15/4.00  fof(f2,axiom,(
% 27.15/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f16,plain,(
% 27.15/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(rectify,[],[f2])).
% 27.15/4.00  
% 27.15/4.00  fof(f19,plain,(
% 27.15/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(ennf_transformation,[],[f16])).
% 27.15/4.00  
% 27.15/4.00  fof(f26,plain,(
% 27.15/4.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 27.15/4.00    introduced(choice_axiom,[])).
% 27.15/4.00  
% 27.15/4.00  fof(f27,plain,(
% 27.15/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).
% 27.15/4.00  
% 27.15/4.00  fof(f36,plain,(
% 27.15/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.15/4.00    inference(cnf_transformation,[],[f27])).
% 27.15/4.00  
% 27.15/4.00  fof(f5,axiom,(
% 27.15/4.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f39,plain,(
% 27.15/4.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f5])).
% 27.15/4.00  
% 27.15/4.00  fof(f7,axiom,(
% 27.15/4.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f17,plain,(
% 27.15/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 27.15/4.00    inference(unused_predicate_definition_removal,[],[f7])).
% 27.15/4.00  
% 27.15/4.00  fof(f21,plain,(
% 27.15/4.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 27.15/4.00    inference(ennf_transformation,[],[f17])).
% 27.15/4.00  
% 27.15/4.00  fof(f41,plain,(
% 27.15/4.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f21])).
% 27.15/4.00  
% 27.15/4.00  fof(f10,axiom,(
% 27.15/4.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f44,plain,(
% 27.15/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f10])).
% 27.15/4.00  
% 27.15/4.00  fof(f4,axiom,(
% 27.15/4.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f38,plain,(
% 27.15/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f4])).
% 27.15/4.00  
% 27.15/4.00  fof(f9,axiom,(
% 27.15/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f43,plain,(
% 27.15/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.15/4.00    inference(cnf_transformation,[],[f9])).
% 27.15/4.00  
% 27.15/4.00  fof(f8,axiom,(
% 27.15/4.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f42,plain,(
% 27.15/4.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.15/4.00    inference(cnf_transformation,[],[f8])).
% 27.15/4.00  
% 27.15/4.00  fof(f12,axiom,(
% 27.15/4.00    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f22,plain,(
% 27.15/4.00    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 27.15/4.00    inference(ennf_transformation,[],[f12])).
% 27.15/4.00  
% 27.15/4.00  fof(f46,plain,(
% 27.15/4.00    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f22])).
% 27.15/4.00  
% 27.15/4.00  fof(f1,axiom,(
% 27.15/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f15,plain,(
% 27.15/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(rectify,[],[f1])).
% 27.15/4.00  
% 27.15/4.00  fof(f18,plain,(
% 27.15/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(ennf_transformation,[],[f15])).
% 27.15/4.00  
% 27.15/4.00  fof(f24,plain,(
% 27.15/4.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.15/4.00    introduced(choice_axiom,[])).
% 27.15/4.00  
% 27.15/4.00  fof(f25,plain,(
% 27.15/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 27.15/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).
% 27.15/4.00  
% 27.15/4.00  fof(f32,plain,(
% 27.15/4.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f25])).
% 27.15/4.00  
% 27.15/4.00  fof(f6,axiom,(
% 27.15/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f40,plain,(
% 27.15/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.15/4.00    inference(cnf_transformation,[],[f6])).
% 27.15/4.00  
% 27.15/4.00  fof(f34,plain,(
% 27.15/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f25])).
% 27.15/4.00  
% 27.15/4.00  fof(f11,axiom,(
% 27.15/4.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 27.15/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.15/4.00  
% 27.15/4.00  fof(f45,plain,(
% 27.15/4.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f11])).
% 27.15/4.00  
% 27.15/4.00  fof(f33,plain,(
% 27.15/4.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 27.15/4.00    inference(cnf_transformation,[],[f25])).
% 27.15/4.00  
% 27.15/4.00  fof(f48,plain,(
% 27.15/4.00    ~r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4))),
% 27.15/4.00    inference(cnf_transformation,[],[f31])).
% 27.15/4.00  
% 27.15/4.00  cnf(c_16,negated_conjecture,
% 27.15/4.00      ( r1_xboole_0(sK3,sK4) ),
% 27.15/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_342,plain,
% 27.15/4.00      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_5,plain,
% 27.15/4.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 27.15/4.00      inference(cnf_transformation,[],[f37]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_348,plain,
% 27.15/4.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_3,plain,
% 27.15/4.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 27.15/4.00      inference(cnf_transformation,[],[f36]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_350,plain,
% 27.15/4.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 27.15/4.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_5606,plain,
% 27.15/4.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_348,c_350]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_79983,plain,
% 27.15/4.00      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_342,c_5606]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_7,plain,
% 27.15/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 27.15/4.00      inference(cnf_transformation,[],[f39]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_347,plain,
% 27.15/4.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_9,plain,
% 27.15/4.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.15/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_346,plain,
% 27.15/4.00      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1528,plain,
% 27.15/4.00      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_347,c_346]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_12,plain,
% 27.15/4.00      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.15/4.00      inference(cnf_transformation,[],[f44]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1808,plain,
% 27.15/4.00      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_1528,c_12]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_6,plain,
% 27.15/4.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 27.15/4.00      inference(cnf_transformation,[],[f38]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_2035,plain,
% 27.15/4.00      ( k3_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_1808,c_6]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_11,plain,
% 27.15/4.00      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 27.15/4.00      inference(cnf_transformation,[],[f43]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_3882,plain,
% 27.15/4.00      ( k4_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_2035,c_11]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10,plain,
% 27.15/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.15/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_3895,plain,
% 27.15/4.00      ( k4_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X0,X1)))) = X0 ),
% 27.15/4.00      inference(light_normalisation,[status(thm)],[c_3882,c_10]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_12319,plain,
% 27.15/4.00      ( k4_xboole_0(X0,k3_xboole_0(k4_xboole_0(X1,k3_xboole_0(X2,X0)),X2)) = X0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_3895,c_3895]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_80346,plain,
% 27.15/4.00      ( k4_xboole_0(sK4,k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK3)) = sK4 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_79983,c_12319]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_80361,plain,
% 27.15/4.00      ( k4_xboole_0(sK4,k3_xboole_0(X0,sK3)) = sK4 ),
% 27.15/4.00      inference(light_normalisation,[status(thm)],[c_80346,c_10]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_14,plain,
% 27.15/4.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 27.15/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_344,plain,
% 27.15/4.00      ( r1_xboole_0(X0,X1) = iProver_top
% 27.15/4.00      | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_2027,plain,
% 27.15/4.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top
% 27.15/4.00      | r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) != iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_1808,c_344]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_2,plain,
% 27.15/4.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 27.15/4.00      inference(cnf_transformation,[],[f32]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_351,plain,
% 27.15/4.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 27.15/4.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_80318,plain,
% 27.15/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.15/4.00      | r1_xboole_0(sK3,sK4) != iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_79983,c_350]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1807,plain,
% 27.15/4.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_1528,c_10]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_5609,plain,
% 27.15/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 27.15/4.00      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_1807,c_350]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_123,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_122,plain,( X0 = X0 ),theory(equality) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_2322,plain,
% 27.15/4.00      ( X0 != X1 | X1 = X0 ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_123,c_122]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_8,plain,
% 27.15/4.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.15/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_4189,plain,
% 27.15/4.00      ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_2322,c_8]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_124,plain,
% 27.15/4.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.15/4.00      theory(equality) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1872,plain,
% 27.15/4.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_124,c_122]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10412,plain,
% 27.15/4.00      ( ~ r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)
% 27.15/4.00      | r1_xboole_0(k1_xboole_0,X1) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_4189,c_1872]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10427,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) != iProver_top
% 27.15/4.00      | r1_xboole_0(k1_xboole_0,X1) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_10412]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_0,plain,
% 27.15/4.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 27.15/4.00      inference(cnf_transformation,[],[f34]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_13,plain,
% 27.15/4.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 27.15/4.00      inference(cnf_transformation,[],[f45]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1223,plain,
% 27.15/4.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_0,c_13]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_3956,plain,
% 27.15/4.00      ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_1223,c_2]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1,plain,
% 27.15/4.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 27.15/4.00      inference(cnf_transformation,[],[f33]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10949,plain,
% 27.15/4.00      ( r1_xboole_0(k1_xboole_0,X0) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_3956,c_1]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_1893,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)
% 27.15/4.00      | ~ r1_xboole_0(k1_xboole_0,X1) ),
% 27.15/4.00      inference(resolution,[status(thm)],[c_1872,c_8]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10954,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 27.15/4.00      inference(backward_subsumption_resolution,[status(thm)],[c_10949,c_1893]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_10967,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) = iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_10954]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_80562,plain,
% 27.15/4.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 27.15/4.00      inference(global_propositional_subsumption,
% 27.15/4.00                [status(thm)],
% 27.15/4.00                [c_80318,c_5609,c_10427,c_10967]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_80568,plain,
% 27.15/4.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_351,c_80562]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_95592,plain,
% 27.15/4.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 27.15/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_2027,c_80568]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_95598,plain,
% 27.15/4.00      ( r1_xboole_0(X0,k3_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_12,c_95592]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_97890,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(X0,sK3),k3_xboole_0(X1,sK4)) = iProver_top ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_80361,c_95598]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_15,negated_conjecture,
% 27.15/4.00      ( ~ r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) ),
% 27.15/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_343,plain,
% 27.15/4.00      ( r1_xboole_0(k3_xboole_0(sK5,sK3),k3_xboole_0(sK5,sK4)) != iProver_top ),
% 27.15/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.15/4.00  
% 27.15/4.00  cnf(c_137470,plain,
% 27.15/4.00      ( $false ),
% 27.15/4.00      inference(superposition,[status(thm)],[c_97890,c_343]) ).
% 27.15/4.00  
% 27.15/4.00  
% 27.15/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.15/4.00  
% 27.15/4.00  ------                               Statistics
% 27.15/4.00  
% 27.15/4.00  ------ Selected
% 27.15/4.00  
% 27.15/4.00  total_time:                             3.36
% 27.15/4.00  
%------------------------------------------------------------------------------
