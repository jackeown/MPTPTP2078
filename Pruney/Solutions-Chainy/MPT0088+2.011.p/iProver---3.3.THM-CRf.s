%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:34 EST 2020

% Result     : Theorem 15.62s
% Output     : CNFRefutation 15.62s
% Verified   : 
% Statistics : Number of formulae       :  151 (2998 expanded)
%              Number of clauses        :  102 ( 976 expanded)
%              Number of leaves         :   21 ( 865 expanded)
%              Depth                    :   28
%              Number of atoms          :  209 (3063 expanded)
%              Number of equality atoms :  148 (2990 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
      & r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
    & r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f25])).

fof(f42,plain,(
    r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f23])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f38,f36,f36,f36])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_302,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_305,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_307,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3617,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_307])).

cnf(c_66418,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_302,c_3617])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_697,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_12])).

cnf(c_67279,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_66418,c_697])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_308,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_449,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_67366,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_67279,c_7,c_308,c_449])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_698,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9,c_12])).

cnf(c_716,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_698,c_9])).

cnf(c_717,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_716,c_9,c_12])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_603,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_11])).

cnf(c_613,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_603,c_9])).

cnf(c_703,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_700,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_8,c_12])).

cnf(c_713,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_700,c_12])).

cnf(c_11430,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_613,c_703,c_713])).

cnf(c_701,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9,c_12])).

cnf(c_711,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_701,c_9])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_712,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_711,c_9,c_10,c_12])).

cnf(c_702,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_308,c_12])).

cnf(c_710,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_702,c_7])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_705,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_12,c_6])).

cnf(c_709,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_705,c_7,c_308])).

cnf(c_1537,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_710,c_709,c_710])).

cnf(c_1568,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1537,c_1537])).

cnf(c_1828,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1568,c_12])).

cnf(c_1834,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1828,c_4,c_308])).

cnf(c_11431,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_11430,c_712,c_1834])).

cnf(c_591,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_11590,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11431,c_591])).

cnf(c_11685,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11590,c_8])).

cnf(c_23552,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_11685,c_703])).

cnf(c_4780,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) ),
    inference(superposition,[status(thm)],[c_1834,c_12])).

cnf(c_4876,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_4780,c_12])).

cnf(c_23644,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X3)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_23552,c_4876])).

cnf(c_19421,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_697,c_591])).

cnf(c_19565,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_19421,c_703])).

cnf(c_23645,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_23644,c_703,c_19565])).

cnf(c_23646,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_23645,c_697])).

cnf(c_39707,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X3,X2)))) ),
    inference(demodulation,[status(thm)],[c_717,c_23646])).

cnf(c_39773,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[status(thm)],[c_308,c_39707])).

cnf(c_39788,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1)))) ),
    inference(superposition,[status(thm)],[c_1834,c_39707])).

cnf(c_4814,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) ),
    inference(superposition,[status(thm)],[c_1834,c_12])).

cnf(c_4866,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_4814,c_12])).

cnf(c_41502,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_39788,c_4866])).

cnf(c_1573,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1537,c_12])).

cnf(c_1581,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1573,c_308])).

cnf(c_1582,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1581,c_4])).

cnf(c_19448,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_697,c_697])).

cnf(c_11802,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11685,c_709])).

cnf(c_19559,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_19448,c_11802])).

cnf(c_41503,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_41502,c_1582,c_4876,c_19559,c_19565])).

cnf(c_41534,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X1)),X1))) ),
    inference(demodulation,[status(thm)],[c_39773,c_41503])).

cnf(c_2466,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_10,c_1582])).

cnf(c_936,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_1029,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_936,c_591])).

cnf(c_2551,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_2466,c_1029])).

cnf(c_41535,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_41534,c_7,c_591,c_703,c_1568,c_2551,c_4876,c_19565])).

cnf(c_41536,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_41535,c_1834])).

cnf(c_67518,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_67366,c_41536])).

cnf(c_1557,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_1537,c_12])).

cnf(c_693,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_12])).

cnf(c_820,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_709,c_4])).

cnf(c_1589,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_1557,c_7,c_693,c_820])).

cnf(c_13,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_304,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1893,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_304])).

cnf(c_72904,plain,
    ( r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_67518,c_1893])).

cnf(c_73304,plain,
    ( r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72904])).

cnf(c_184,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_317,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_335,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_354,plain,
    ( ~ r1_xboole_0(sK3,k4_xboole_0(X0,X1))
    | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_2573,plain,
    ( ~ r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0))
    | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_2574,plain,
    ( k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
    | sK3 != sK3
    | r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)) != iProver_top
    | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2573])).

cnf(c_758,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) = k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_353,plain,
    ( X0 != X1
    | k4_xboole_0(sK2,sK4) != X1
    | k4_xboole_0(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_375,plain,
    ( X0 != k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,sK4) = X0
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_649,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) != k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_436,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_365,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73304,c_2574,c_758,c_649,c_436,c_365,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.62/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.62/2.48  
% 15.62/2.48  ------  iProver source info
% 15.62/2.48  
% 15.62/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.62/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.62/2.48  git: non_committed_changes: false
% 15.62/2.48  git: last_make_outside_of_git: false
% 15.62/2.48  
% 15.62/2.48  ------ 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options
% 15.62/2.48  
% 15.62/2.48  --out_options                           all
% 15.62/2.48  --tptp_safe_out                         true
% 15.62/2.48  --problem_path                          ""
% 15.62/2.48  --include_path                          ""
% 15.62/2.48  --clausifier                            res/vclausify_rel
% 15.62/2.48  --clausifier_options                    ""
% 15.62/2.48  --stdin                                 false
% 15.62/2.48  --stats_out                             all
% 15.62/2.48  
% 15.62/2.48  ------ General Options
% 15.62/2.48  
% 15.62/2.48  --fof                                   false
% 15.62/2.48  --time_out_real                         305.
% 15.62/2.48  --time_out_virtual                      -1.
% 15.62/2.48  --symbol_type_check                     false
% 15.62/2.48  --clausify_out                          false
% 15.62/2.48  --sig_cnt_out                           false
% 15.62/2.48  --trig_cnt_out                          false
% 15.62/2.48  --trig_cnt_out_tolerance                1.
% 15.62/2.48  --trig_cnt_out_sk_spl                   false
% 15.62/2.48  --abstr_cl_out                          false
% 15.62/2.48  
% 15.62/2.48  ------ Global Options
% 15.62/2.48  
% 15.62/2.48  --schedule                              default
% 15.62/2.48  --add_important_lit                     false
% 15.62/2.48  --prop_solver_per_cl                    1000
% 15.62/2.48  --min_unsat_core                        false
% 15.62/2.48  --soft_assumptions                      false
% 15.62/2.48  --soft_lemma_size                       3
% 15.62/2.48  --prop_impl_unit_size                   0
% 15.62/2.48  --prop_impl_unit                        []
% 15.62/2.48  --share_sel_clauses                     true
% 15.62/2.48  --reset_solvers                         false
% 15.62/2.48  --bc_imp_inh                            [conj_cone]
% 15.62/2.48  --conj_cone_tolerance                   3.
% 15.62/2.48  --extra_neg_conj                        none
% 15.62/2.48  --large_theory_mode                     true
% 15.62/2.48  --prolific_symb_bound                   200
% 15.62/2.48  --lt_threshold                          2000
% 15.62/2.48  --clause_weak_htbl                      true
% 15.62/2.48  --gc_record_bc_elim                     false
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing Options
% 15.62/2.48  
% 15.62/2.48  --preprocessing_flag                    true
% 15.62/2.48  --time_out_prep_mult                    0.1
% 15.62/2.48  --splitting_mode                        input
% 15.62/2.48  --splitting_grd                         true
% 15.62/2.48  --splitting_cvd                         false
% 15.62/2.48  --splitting_cvd_svl                     false
% 15.62/2.48  --splitting_nvd                         32
% 15.62/2.48  --sub_typing                            true
% 15.62/2.48  --prep_gs_sim                           true
% 15.62/2.48  --prep_unflatten                        true
% 15.62/2.48  --prep_res_sim                          true
% 15.62/2.48  --prep_upred                            true
% 15.62/2.48  --prep_sem_filter                       exhaustive
% 15.62/2.48  --prep_sem_filter_out                   false
% 15.62/2.48  --pred_elim                             true
% 15.62/2.48  --res_sim_input                         true
% 15.62/2.48  --eq_ax_congr_red                       true
% 15.62/2.48  --pure_diseq_elim                       true
% 15.62/2.48  --brand_transform                       false
% 15.62/2.48  --non_eq_to_eq                          false
% 15.62/2.48  --prep_def_merge                        true
% 15.62/2.48  --prep_def_merge_prop_impl              false
% 15.62/2.48  --prep_def_merge_mbd                    true
% 15.62/2.48  --prep_def_merge_tr_red                 false
% 15.62/2.48  --prep_def_merge_tr_cl                  false
% 15.62/2.48  --smt_preprocessing                     true
% 15.62/2.48  --smt_ac_axioms                         fast
% 15.62/2.48  --preprocessed_out                      false
% 15.62/2.48  --preprocessed_stats                    false
% 15.62/2.48  
% 15.62/2.48  ------ Abstraction refinement Options
% 15.62/2.48  
% 15.62/2.48  --abstr_ref                             []
% 15.62/2.48  --abstr_ref_prep                        false
% 15.62/2.48  --abstr_ref_until_sat                   false
% 15.62/2.48  --abstr_ref_sig_restrict                funpre
% 15.62/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.48  --abstr_ref_under                       []
% 15.62/2.48  
% 15.62/2.48  ------ SAT Options
% 15.62/2.48  
% 15.62/2.48  --sat_mode                              false
% 15.62/2.48  --sat_fm_restart_options                ""
% 15.62/2.48  --sat_gr_def                            false
% 15.62/2.48  --sat_epr_types                         true
% 15.62/2.48  --sat_non_cyclic_types                  false
% 15.62/2.48  --sat_finite_models                     false
% 15.62/2.48  --sat_fm_lemmas                         false
% 15.62/2.48  --sat_fm_prep                           false
% 15.62/2.48  --sat_fm_uc_incr                        true
% 15.62/2.48  --sat_out_model                         small
% 15.62/2.48  --sat_out_clauses                       false
% 15.62/2.48  
% 15.62/2.48  ------ QBF Options
% 15.62/2.48  
% 15.62/2.48  --qbf_mode                              false
% 15.62/2.48  --qbf_elim_univ                         false
% 15.62/2.48  --qbf_dom_inst                          none
% 15.62/2.48  --qbf_dom_pre_inst                      false
% 15.62/2.48  --qbf_sk_in                             false
% 15.62/2.48  --qbf_pred_elim                         true
% 15.62/2.48  --qbf_split                             512
% 15.62/2.48  
% 15.62/2.48  ------ BMC1 Options
% 15.62/2.48  
% 15.62/2.48  --bmc1_incremental                      false
% 15.62/2.48  --bmc1_axioms                           reachable_all
% 15.62/2.48  --bmc1_min_bound                        0
% 15.62/2.48  --bmc1_max_bound                        -1
% 15.62/2.48  --bmc1_max_bound_default                -1
% 15.62/2.48  --bmc1_symbol_reachability              true
% 15.62/2.48  --bmc1_property_lemmas                  false
% 15.62/2.48  --bmc1_k_induction                      false
% 15.62/2.48  --bmc1_non_equiv_states                 false
% 15.62/2.48  --bmc1_deadlock                         false
% 15.62/2.48  --bmc1_ucm                              false
% 15.62/2.48  --bmc1_add_unsat_core                   none
% 15.62/2.48  --bmc1_unsat_core_children              false
% 15.62/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.48  --bmc1_out_stat                         full
% 15.62/2.48  --bmc1_ground_init                      false
% 15.62/2.48  --bmc1_pre_inst_next_state              false
% 15.62/2.48  --bmc1_pre_inst_state                   false
% 15.62/2.48  --bmc1_pre_inst_reach_state             false
% 15.62/2.48  --bmc1_out_unsat_core                   false
% 15.62/2.48  --bmc1_aig_witness_out                  false
% 15.62/2.48  --bmc1_verbose                          false
% 15.62/2.48  --bmc1_dump_clauses_tptp                false
% 15.62/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.48  --bmc1_dump_file                        -
% 15.62/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.48  --bmc1_ucm_extend_mode                  1
% 15.62/2.48  --bmc1_ucm_init_mode                    2
% 15.62/2.48  --bmc1_ucm_cone_mode                    none
% 15.62/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.48  --bmc1_ucm_relax_model                  4
% 15.62/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.48  --bmc1_ucm_layered_model                none
% 15.62/2.48  --bmc1_ucm_max_lemma_size               10
% 15.62/2.48  
% 15.62/2.48  ------ AIG Options
% 15.62/2.48  
% 15.62/2.48  --aig_mode                              false
% 15.62/2.48  
% 15.62/2.48  ------ Instantiation Options
% 15.62/2.48  
% 15.62/2.48  --instantiation_flag                    true
% 15.62/2.48  --inst_sos_flag                         true
% 15.62/2.48  --inst_sos_phase                        true
% 15.62/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel_side                     num_symb
% 15.62/2.48  --inst_solver_per_active                1400
% 15.62/2.48  --inst_solver_calls_frac                1.
% 15.62/2.48  --inst_passive_queue_type               priority_queues
% 15.62/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.48  --inst_passive_queues_freq              [25;2]
% 15.62/2.48  --inst_dismatching                      true
% 15.62/2.48  --inst_eager_unprocessed_to_passive     true
% 15.62/2.48  --inst_prop_sim_given                   true
% 15.62/2.48  --inst_prop_sim_new                     false
% 15.62/2.48  --inst_subs_new                         false
% 15.62/2.48  --inst_eq_res_simp                      false
% 15.62/2.48  --inst_subs_given                       false
% 15.62/2.48  --inst_orphan_elimination               true
% 15.62/2.48  --inst_learning_loop_flag               true
% 15.62/2.48  --inst_learning_start                   3000
% 15.62/2.48  --inst_learning_factor                  2
% 15.62/2.48  --inst_start_prop_sim_after_learn       3
% 15.62/2.48  --inst_sel_renew                        solver
% 15.62/2.48  --inst_lit_activity_flag                true
% 15.62/2.48  --inst_restr_to_given                   false
% 15.62/2.48  --inst_activity_threshold               500
% 15.62/2.48  --inst_out_proof                        true
% 15.62/2.48  
% 15.62/2.48  ------ Resolution Options
% 15.62/2.48  
% 15.62/2.48  --resolution_flag                       true
% 15.62/2.48  --res_lit_sel                           adaptive
% 15.62/2.48  --res_lit_sel_side                      none
% 15.62/2.48  --res_ordering                          kbo
% 15.62/2.48  --res_to_prop_solver                    active
% 15.62/2.48  --res_prop_simpl_new                    false
% 15.62/2.48  --res_prop_simpl_given                  true
% 15.62/2.48  --res_passive_queue_type                priority_queues
% 15.62/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.48  --res_passive_queues_freq               [15;5]
% 15.62/2.48  --res_forward_subs                      full
% 15.62/2.48  --res_backward_subs                     full
% 15.62/2.48  --res_forward_subs_resolution           true
% 15.62/2.48  --res_backward_subs_resolution          true
% 15.62/2.48  --res_orphan_elimination                true
% 15.62/2.48  --res_time_limit                        2.
% 15.62/2.48  --res_out_proof                         true
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Options
% 15.62/2.48  
% 15.62/2.48  --superposition_flag                    true
% 15.62/2.48  --sup_passive_queue_type                priority_queues
% 15.62/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.62/2.48  --demod_completeness_check              fast
% 15.62/2.48  --demod_use_ground                      true
% 15.62/2.48  --sup_to_prop_solver                    passive
% 15.62/2.48  --sup_prop_simpl_new                    true
% 15.62/2.48  --sup_prop_simpl_given                  true
% 15.62/2.48  --sup_fun_splitting                     true
% 15.62/2.48  --sup_smt_interval                      50000
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Simplification Setup
% 15.62/2.48  
% 15.62/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.62/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.62/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.62/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.62/2.48  --sup_immed_triv                        [TrivRules]
% 15.62/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_bw_main                     []
% 15.62/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.62/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_input_bw                          []
% 15.62/2.48  
% 15.62/2.48  ------ Combination Options
% 15.62/2.48  
% 15.62/2.48  --comb_res_mult                         3
% 15.62/2.48  --comb_sup_mult                         2
% 15.62/2.48  --comb_inst_mult                        10
% 15.62/2.48  
% 15.62/2.48  ------ Debug Options
% 15.62/2.48  
% 15.62/2.48  --dbg_backtrace                         false
% 15.62/2.48  --dbg_dump_prop_clauses                 false
% 15.62/2.48  --dbg_dump_prop_clauses_file            -
% 15.62/2.48  --dbg_out_stat                          false
% 15.62/2.48  ------ Parsing...
% 15.62/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.62/2.48  ------ Proving...
% 15.62/2.48  ------ Problem Properties 
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  clauses                                 16
% 15.62/2.48  conjectures                             2
% 15.62/2.48  EPR                                     0
% 15.62/2.48  Horn                                    14
% 15.62/2.48  unary                                   13
% 15.62/2.48  binary                                  3
% 15.62/2.48  lits                                    19
% 15.62/2.48  lits eq                                 11
% 15.62/2.48  fd_pure                                 0
% 15.62/2.48  fd_pseudo                               0
% 15.62/2.48  fd_cond                                 1
% 15.62/2.48  fd_pseudo_cond                          0
% 15.62/2.48  AC symbols                              0
% 15.62/2.48  
% 15.62/2.48  ------ Schedule dynamic 5 is on 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  ------ 
% 15.62/2.48  Current options:
% 15.62/2.48  ------ 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options
% 15.62/2.48  
% 15.62/2.48  --out_options                           all
% 15.62/2.48  --tptp_safe_out                         true
% 15.62/2.48  --problem_path                          ""
% 15.62/2.48  --include_path                          ""
% 15.62/2.48  --clausifier                            res/vclausify_rel
% 15.62/2.48  --clausifier_options                    ""
% 15.62/2.48  --stdin                                 false
% 15.62/2.48  --stats_out                             all
% 15.62/2.48  
% 15.62/2.48  ------ General Options
% 15.62/2.48  
% 15.62/2.48  --fof                                   false
% 15.62/2.48  --time_out_real                         305.
% 15.62/2.48  --time_out_virtual                      -1.
% 15.62/2.48  --symbol_type_check                     false
% 15.62/2.48  --clausify_out                          false
% 15.62/2.48  --sig_cnt_out                           false
% 15.62/2.48  --trig_cnt_out                          false
% 15.62/2.48  --trig_cnt_out_tolerance                1.
% 15.62/2.48  --trig_cnt_out_sk_spl                   false
% 15.62/2.48  --abstr_cl_out                          false
% 15.62/2.48  
% 15.62/2.48  ------ Global Options
% 15.62/2.48  
% 15.62/2.48  --schedule                              default
% 15.62/2.48  --add_important_lit                     false
% 15.62/2.48  --prop_solver_per_cl                    1000
% 15.62/2.48  --min_unsat_core                        false
% 15.62/2.48  --soft_assumptions                      false
% 15.62/2.48  --soft_lemma_size                       3
% 15.62/2.48  --prop_impl_unit_size                   0
% 15.62/2.48  --prop_impl_unit                        []
% 15.62/2.48  --share_sel_clauses                     true
% 15.62/2.48  --reset_solvers                         false
% 15.62/2.48  --bc_imp_inh                            [conj_cone]
% 15.62/2.48  --conj_cone_tolerance                   3.
% 15.62/2.48  --extra_neg_conj                        none
% 15.62/2.48  --large_theory_mode                     true
% 15.62/2.48  --prolific_symb_bound                   200
% 15.62/2.48  --lt_threshold                          2000
% 15.62/2.48  --clause_weak_htbl                      true
% 15.62/2.48  --gc_record_bc_elim                     false
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing Options
% 15.62/2.48  
% 15.62/2.48  --preprocessing_flag                    true
% 15.62/2.48  --time_out_prep_mult                    0.1
% 15.62/2.48  --splitting_mode                        input
% 15.62/2.48  --splitting_grd                         true
% 15.62/2.48  --splitting_cvd                         false
% 15.62/2.48  --splitting_cvd_svl                     false
% 15.62/2.48  --splitting_nvd                         32
% 15.62/2.48  --sub_typing                            true
% 15.62/2.48  --prep_gs_sim                           true
% 15.62/2.48  --prep_unflatten                        true
% 15.62/2.48  --prep_res_sim                          true
% 15.62/2.48  --prep_upred                            true
% 15.62/2.48  --prep_sem_filter                       exhaustive
% 15.62/2.48  --prep_sem_filter_out                   false
% 15.62/2.48  --pred_elim                             true
% 15.62/2.48  --res_sim_input                         true
% 15.62/2.48  --eq_ax_congr_red                       true
% 15.62/2.48  --pure_diseq_elim                       true
% 15.62/2.48  --brand_transform                       false
% 15.62/2.48  --non_eq_to_eq                          false
% 15.62/2.48  --prep_def_merge                        true
% 15.62/2.48  --prep_def_merge_prop_impl              false
% 15.62/2.48  --prep_def_merge_mbd                    true
% 15.62/2.48  --prep_def_merge_tr_red                 false
% 15.62/2.48  --prep_def_merge_tr_cl                  false
% 15.62/2.48  --smt_preprocessing                     true
% 15.62/2.48  --smt_ac_axioms                         fast
% 15.62/2.48  --preprocessed_out                      false
% 15.62/2.48  --preprocessed_stats                    false
% 15.62/2.48  
% 15.62/2.48  ------ Abstraction refinement Options
% 15.62/2.48  
% 15.62/2.48  --abstr_ref                             []
% 15.62/2.48  --abstr_ref_prep                        false
% 15.62/2.48  --abstr_ref_until_sat                   false
% 15.62/2.48  --abstr_ref_sig_restrict                funpre
% 15.62/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.48  --abstr_ref_under                       []
% 15.62/2.48  
% 15.62/2.48  ------ SAT Options
% 15.62/2.48  
% 15.62/2.48  --sat_mode                              false
% 15.62/2.48  --sat_fm_restart_options                ""
% 15.62/2.48  --sat_gr_def                            false
% 15.62/2.48  --sat_epr_types                         true
% 15.62/2.48  --sat_non_cyclic_types                  false
% 15.62/2.48  --sat_finite_models                     false
% 15.62/2.48  --sat_fm_lemmas                         false
% 15.62/2.48  --sat_fm_prep                           false
% 15.62/2.48  --sat_fm_uc_incr                        true
% 15.62/2.48  --sat_out_model                         small
% 15.62/2.48  --sat_out_clauses                       false
% 15.62/2.48  
% 15.62/2.48  ------ QBF Options
% 15.62/2.48  
% 15.62/2.48  --qbf_mode                              false
% 15.62/2.48  --qbf_elim_univ                         false
% 15.62/2.48  --qbf_dom_inst                          none
% 15.62/2.48  --qbf_dom_pre_inst                      false
% 15.62/2.48  --qbf_sk_in                             false
% 15.62/2.48  --qbf_pred_elim                         true
% 15.62/2.48  --qbf_split                             512
% 15.62/2.48  
% 15.62/2.48  ------ BMC1 Options
% 15.62/2.48  
% 15.62/2.48  --bmc1_incremental                      false
% 15.62/2.48  --bmc1_axioms                           reachable_all
% 15.62/2.48  --bmc1_min_bound                        0
% 15.62/2.48  --bmc1_max_bound                        -1
% 15.62/2.48  --bmc1_max_bound_default                -1
% 15.62/2.48  --bmc1_symbol_reachability              true
% 15.62/2.48  --bmc1_property_lemmas                  false
% 15.62/2.48  --bmc1_k_induction                      false
% 15.62/2.48  --bmc1_non_equiv_states                 false
% 15.62/2.48  --bmc1_deadlock                         false
% 15.62/2.48  --bmc1_ucm                              false
% 15.62/2.48  --bmc1_add_unsat_core                   none
% 15.62/2.48  --bmc1_unsat_core_children              false
% 15.62/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.48  --bmc1_out_stat                         full
% 15.62/2.48  --bmc1_ground_init                      false
% 15.62/2.48  --bmc1_pre_inst_next_state              false
% 15.62/2.48  --bmc1_pre_inst_state                   false
% 15.62/2.48  --bmc1_pre_inst_reach_state             false
% 15.62/2.48  --bmc1_out_unsat_core                   false
% 15.62/2.48  --bmc1_aig_witness_out                  false
% 15.62/2.48  --bmc1_verbose                          false
% 15.62/2.48  --bmc1_dump_clauses_tptp                false
% 15.62/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.48  --bmc1_dump_file                        -
% 15.62/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.48  --bmc1_ucm_extend_mode                  1
% 15.62/2.48  --bmc1_ucm_init_mode                    2
% 15.62/2.48  --bmc1_ucm_cone_mode                    none
% 15.62/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.48  --bmc1_ucm_relax_model                  4
% 15.62/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.48  --bmc1_ucm_layered_model                none
% 15.62/2.48  --bmc1_ucm_max_lemma_size               10
% 15.62/2.48  
% 15.62/2.48  ------ AIG Options
% 15.62/2.48  
% 15.62/2.48  --aig_mode                              false
% 15.62/2.48  
% 15.62/2.48  ------ Instantiation Options
% 15.62/2.48  
% 15.62/2.48  --instantiation_flag                    true
% 15.62/2.48  --inst_sos_flag                         true
% 15.62/2.48  --inst_sos_phase                        true
% 15.62/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel_side                     none
% 15.62/2.48  --inst_solver_per_active                1400
% 15.62/2.48  --inst_solver_calls_frac                1.
% 15.62/2.48  --inst_passive_queue_type               priority_queues
% 15.62/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.48  --inst_passive_queues_freq              [25;2]
% 15.62/2.48  --inst_dismatching                      true
% 15.62/2.48  --inst_eager_unprocessed_to_passive     true
% 15.62/2.48  --inst_prop_sim_given                   true
% 15.62/2.48  --inst_prop_sim_new                     false
% 15.62/2.48  --inst_subs_new                         false
% 15.62/2.48  --inst_eq_res_simp                      false
% 15.62/2.48  --inst_subs_given                       false
% 15.62/2.48  --inst_orphan_elimination               true
% 15.62/2.48  --inst_learning_loop_flag               true
% 15.62/2.48  --inst_learning_start                   3000
% 15.62/2.48  --inst_learning_factor                  2
% 15.62/2.48  --inst_start_prop_sim_after_learn       3
% 15.62/2.48  --inst_sel_renew                        solver
% 15.62/2.48  --inst_lit_activity_flag                true
% 15.62/2.48  --inst_restr_to_given                   false
% 15.62/2.48  --inst_activity_threshold               500
% 15.62/2.48  --inst_out_proof                        true
% 15.62/2.48  
% 15.62/2.48  ------ Resolution Options
% 15.62/2.48  
% 15.62/2.48  --resolution_flag                       false
% 15.62/2.48  --res_lit_sel                           adaptive
% 15.62/2.48  --res_lit_sel_side                      none
% 15.62/2.48  --res_ordering                          kbo
% 15.62/2.48  --res_to_prop_solver                    active
% 15.62/2.48  --res_prop_simpl_new                    false
% 15.62/2.48  --res_prop_simpl_given                  true
% 15.62/2.48  --res_passive_queue_type                priority_queues
% 15.62/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.48  --res_passive_queues_freq               [15;5]
% 15.62/2.48  --res_forward_subs                      full
% 15.62/2.48  --res_backward_subs                     full
% 15.62/2.48  --res_forward_subs_resolution           true
% 15.62/2.48  --res_backward_subs_resolution          true
% 15.62/2.48  --res_orphan_elimination                true
% 15.62/2.48  --res_time_limit                        2.
% 15.62/2.48  --res_out_proof                         true
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Options
% 15.62/2.48  
% 15.62/2.48  --superposition_flag                    true
% 15.62/2.48  --sup_passive_queue_type                priority_queues
% 15.62/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.62/2.48  --demod_completeness_check              fast
% 15.62/2.48  --demod_use_ground                      true
% 15.62/2.48  --sup_to_prop_solver                    passive
% 15.62/2.48  --sup_prop_simpl_new                    true
% 15.62/2.48  --sup_prop_simpl_given                  true
% 15.62/2.48  --sup_fun_splitting                     true
% 15.62/2.48  --sup_smt_interval                      50000
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Simplification Setup
% 15.62/2.48  
% 15.62/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.62/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.62/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.62/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.62/2.48  --sup_immed_triv                        [TrivRules]
% 15.62/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_bw_main                     []
% 15.62/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.62/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_input_bw                          []
% 15.62/2.48  
% 15.62/2.48  ------ Combination Options
% 15.62/2.48  
% 15.62/2.48  --comb_res_mult                         3
% 15.62/2.48  --comb_sup_mult                         2
% 15.62/2.48  --comb_inst_mult                        10
% 15.62/2.48  
% 15.62/2.48  ------ Debug Options
% 15.62/2.48  
% 15.62/2.48  --dbg_backtrace                         false
% 15.62/2.48  --dbg_dump_prop_clauses                 false
% 15.62/2.48  --dbg_dump_prop_clauses_file            -
% 15.62/2.48  --dbg_out_stat                          false
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  ------ Proving...
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  % SZS status Theorem for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  fof(f15,conjecture,(
% 15.62/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f16,negated_conjecture,(
% 15.62/2.48    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 15.62/2.48    inference(negated_conjecture,[],[f15])).
% 15.62/2.48  
% 15.62/2.48  fof(f20,plain,(
% 15.62/2.48    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 15.62/2.48    inference(ennf_transformation,[],[f16])).
% 15.62/2.48  
% 15.62/2.48  fof(f25,plain,(
% 15.62/2.48    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) & r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f26,plain,(
% 15.62/2.48    ~r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) & r1_xboole_0(sK2,k4_xboole_0(sK3,sK4))),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f25])).
% 15.62/2.48  
% 15.62/2.48  fof(f42,plain,(
% 15.62/2.48    r1_xboole_0(sK2,k4_xboole_0(sK3,sK4))),
% 15.62/2.48    inference(cnf_transformation,[],[f26])).
% 15.62/2.48  
% 15.62/2.48  fof(f3,axiom,(
% 15.62/2.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f19,plain,(
% 15.62/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 15.62/2.48    inference(ennf_transformation,[],[f3])).
% 15.62/2.48  
% 15.62/2.48  fof(f23,plain,(
% 15.62/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f24,plain,(
% 15.62/2.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f23])).
% 15.62/2.48  
% 15.62/2.48  fof(f30,plain,(
% 15.62/2.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 15.62/2.48    inference(cnf_transformation,[],[f24])).
% 15.62/2.48  
% 15.62/2.48  fof(f2,axiom,(
% 15.62/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f17,plain,(
% 15.62/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.62/2.48    inference(rectify,[],[f2])).
% 15.62/2.48  
% 15.62/2.48  fof(f18,plain,(
% 15.62/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.62/2.48    inference(ennf_transformation,[],[f17])).
% 15.62/2.48  
% 15.62/2.48  fof(f21,plain,(
% 15.62/2.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f22,plain,(
% 15.62/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).
% 15.62/2.48  
% 15.62/2.48  fof(f29,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f22])).
% 15.62/2.48  
% 15.62/2.48  fof(f9,axiom,(
% 15.62/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f36,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f9])).
% 15.62/2.48  
% 15.62/2.48  fof(f44,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.62/2.48    inference(definition_unfolding,[],[f29,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f8,axiom,(
% 15.62/2.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f35,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f8])).
% 15.62/2.48  
% 15.62/2.48  fof(f47,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.62/2.48    inference(definition_unfolding,[],[f35,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f13,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f40,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f13])).
% 15.62/2.48  
% 15.62/2.48  fof(f51,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 15.62/2.48    inference(definition_unfolding,[],[f40,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f7,axiom,(
% 15.62/2.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f34,plain,(
% 15.62/2.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.62/2.48    inference(cnf_transformation,[],[f7])).
% 15.62/2.48  
% 15.62/2.48  fof(f5,axiom,(
% 15.62/2.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f32,plain,(
% 15.62/2.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.62/2.48    inference(cnf_transformation,[],[f5])).
% 15.62/2.48  
% 15.62/2.48  fof(f46,plain,(
% 15.62/2.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 15.62/2.48    inference(definition_unfolding,[],[f32,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f4,axiom,(
% 15.62/2.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f31,plain,(
% 15.62/2.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.62/2.48    inference(cnf_transformation,[],[f4])).
% 15.62/2.48  
% 15.62/2.48  fof(f1,axiom,(
% 15.62/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f27,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f1])).
% 15.62/2.48  
% 15.62/2.48  fof(f10,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f37,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f10])).
% 15.62/2.48  
% 15.62/2.48  fof(f48,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 15.62/2.48    inference(definition_unfolding,[],[f37,f36,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f12,axiom,(
% 15.62/2.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f39,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 15.62/2.48    inference(cnf_transformation,[],[f12])).
% 15.62/2.48  
% 15.62/2.48  fof(f50,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 15.62/2.48    inference(definition_unfolding,[],[f39,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f11,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f38,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f11])).
% 15.62/2.48  
% 15.62/2.48  fof(f49,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 15.62/2.48    inference(definition_unfolding,[],[f38,f36,f36,f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f6,axiom,(
% 15.62/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f33,plain,(
% 15.62/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f6])).
% 15.62/2.48  
% 15.62/2.48  fof(f14,axiom,(
% 15.62/2.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f41,plain,(
% 15.62/2.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f14])).
% 15.62/2.48  
% 15.62/2.48  fof(f43,plain,(
% 15.62/2.48    ~r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))),
% 15.62/2.48    inference(cnf_transformation,[],[f26])).
% 15.62/2.48  
% 15.62/2.48  cnf(c_15,negated_conjecture,
% 15.62/2.48      ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
% 15.62/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_302,plain,
% 15.62/2.48      ( r1_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_3,plain,
% 15.62/2.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f30]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_305,plain,
% 15.62/2.48      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1,plain,
% 15.62/2.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 15.62/2.48      | ~ r1_xboole_0(X1,X2) ),
% 15.62/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_307,plain,
% 15.62/2.48      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 15.62/2.48      | r1_xboole_0(X1,X2) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_3617,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.62/2.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_305,c_307]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_66418,plain,
% 15.62/2.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k1_xboole_0 ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_302,c_3617]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_8,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_12,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.62/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_697,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_8,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_67279,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_66418,c_697]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_7,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f34]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_5,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f46]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_308,plain,
% 15.62/2.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4,plain,
% 15.62/2.48      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f31]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_0,plain,
% 15.62/2.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f27]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_449,plain,
% 15.62/2.48      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_67366,plain,
% 15.62/2.48      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = sK2 ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_67279,c_7,c_308,c_449]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_9,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 15.62/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_698,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_9,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_716,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_698,c_9]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_717,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_716,c_9,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_603,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_9,c_11]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_613,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_603,c_9]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_703,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_700,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_8,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_713,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_700,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11430,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_613,c_703,c_713]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_701,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_9,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_711,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_701,c_9]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_10,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 15.62/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_712,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_711,c_9,c_10,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_702,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_308,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_710,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_702,c_7]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_6,plain,
% 15.62/2.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_705,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_12,c_6]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_709,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_705,c_7,c_308]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1537,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_710,c_709,c_710]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1568,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1537,c_1537]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1828,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1568,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1834,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_1828,c_4,c_308]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11431,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_11430,c_712,c_1834]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_591,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11590,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_11431,c_591]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11685,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_11590,c_8]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23552,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_11685,c_703]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4780,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1834,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4876,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_4780,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23644,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X0,X3)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_23552,c_4876]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_19421,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_697,c_591]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_19565,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_19421,c_703]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23645,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_23644,c_703,c_19565]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23646,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_23645,c_697]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_39707,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X3,X2)))) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_717,c_23646]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_39773,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X2,X1)))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_308,c_39707]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_39788,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1)))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1834,c_39707]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4814,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1834,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4866,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_4814,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_41502,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_39788,c_4866]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1573,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1537,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1581,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_1573,c_308]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1582,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_1581,c_4]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_19448,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_697,c_697]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11802,plain,
% 15.62/2.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_11685,c_709]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_19559,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_19448,c_11802]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_41503,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,X3),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 15.62/2.48      inference(demodulation,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_41502,c_1582,c_4876,c_19559,c_19565]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_41534,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X2,X1),X1)),X1))) ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_39773,c_41503]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_2466,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_10,c_1582]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_936,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1029,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_936,c_591]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_2551,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_2466,c_1029]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_41535,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X2,X1)),X1) ),
% 15.62/2.48      inference(demodulation,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_41534,c_7,c_591,c_703,c_1568,c_2551,c_4876,c_19565]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_41536,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_41535,c_1834]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_67518,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(sK2,sK4) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_67366,c_41536]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1557,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1537,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_693,plain,
% 15.62/2.48      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_7,c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_820,plain,
% 15.62/2.48      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_709,c_4]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1589,plain,
% 15.62/2.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_1557,c_7,c_693,c_820]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_13,plain,
% 15.62/2.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_304,plain,
% 15.62/2.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1893,plain,
% 15.62/2.48      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1589,c_304]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_72904,plain,
% 15.62/2.48      ( r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),X0)) = iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_67518,c_1893]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_73304,plain,
% 15.62/2.48      ( r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)) = iProver_top ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_72904]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_184,plain,
% 15.62/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.62/2.48      theory(equality) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_317,plain,
% 15.62/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != X1
% 15.62/2.48      | sK3 != X0 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_184]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_335,plain,
% 15.62/2.48      ( ~ r1_xboole_0(sK3,X0)
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != X0
% 15.62/2.48      | sK3 != sK3 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_317]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_354,plain,
% 15.62/2.48      ( ~ r1_xboole_0(sK3,k4_xboole_0(X0,X1))
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
% 15.62/2.48      | sK3 != sK3 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_335]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_2573,plain,
% 15.62/2.48      ( ~ r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0))
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4))
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
% 15.62/2.48      | sK3 != sK3 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_354]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_2574,plain,
% 15.62/2.48      ( k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
% 15.62/2.48      | sK3 != sK3
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)) != iProver_top
% 15.62/2.48      | r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_2573]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_758,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) = k4_xboole_0(sK2,sK4) ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_7]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_353,plain,
% 15.62/2.48      ( X0 != X1
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != X1
% 15.62/2.48      | k4_xboole_0(sK2,sK4) = X0 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_182]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_375,plain,
% 15.62/2.48      ( X0 != k4_xboole_0(sK2,sK4)
% 15.62/2.48      | k4_xboole_0(sK2,sK4) = X0
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_353]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_649,plain,
% 15.62/2.48      ( k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) != k4_xboole_0(sK2,sK4)
% 15.62/2.48      | k4_xboole_0(sK2,sK4) = k4_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0)
% 15.62/2.48      | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_375]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_436,plain,
% 15.62/2.48      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_181]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_365,plain,
% 15.62/2.48      ( sK3 = sK3 ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_181]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_14,negated_conjecture,
% 15.62/2.48      ( ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) ),
% 15.62/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_17,plain,
% 15.62/2.48      ( r1_xboole_0(sK3,k4_xboole_0(sK2,sK4)) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(contradiction,plain,
% 15.62/2.48      ( $false ),
% 15.62/2.48      inference(minisat,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_73304,c_2574,c_758,c_649,c_436,c_365,c_17]) ).
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  ------                               Statistics
% 15.62/2.48  
% 15.62/2.48  ------ General
% 15.62/2.48  
% 15.62/2.48  abstr_ref_over_cycles:                  0
% 15.62/2.48  abstr_ref_under_cycles:                 0
% 15.62/2.48  gc_basic_clause_elim:                   0
% 15.62/2.48  forced_gc_time:                         0
% 15.62/2.48  parsing_time:                           0.006
% 15.62/2.48  unif_index_cands_time:                  0.
% 15.62/2.48  unif_index_add_time:                    0.
% 15.62/2.48  orderings_time:                         0.
% 15.62/2.48  out_proof_time:                         0.011
% 15.62/2.48  total_time:                             1.996
% 15.62/2.48  num_of_symbols:                         41
% 15.62/2.48  num_of_terms:                           101110
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing
% 15.62/2.48  
% 15.62/2.48  num_of_splits:                          0
% 15.62/2.48  num_of_split_atoms:                     0
% 15.62/2.48  num_of_reused_defs:                     0
% 15.62/2.48  num_eq_ax_congr_red:                    6
% 15.62/2.48  num_of_sem_filtered_clauses:            1
% 15.62/2.48  num_of_subtypes:                        0
% 15.62/2.48  monotx_restored_types:                  0
% 15.62/2.48  sat_num_of_epr_types:                   0
% 15.62/2.48  sat_num_of_non_cyclic_types:            0
% 15.62/2.48  sat_guarded_non_collapsed_types:        0
% 15.62/2.48  num_pure_diseq_elim:                    0
% 15.62/2.48  simp_replaced_by:                       0
% 15.62/2.48  res_preprocessed:                       61
% 15.62/2.48  prep_upred:                             0
% 15.62/2.48  prep_unflattend:                        12
% 15.62/2.48  smt_new_axioms:                         0
% 15.62/2.48  pred_elim_cands:                        2
% 15.62/2.48  pred_elim:                              0
% 15.62/2.48  pred_elim_cl:                           0
% 15.62/2.48  pred_elim_cycles:                       2
% 15.62/2.48  merged_defs:                            0
% 15.62/2.48  merged_defs_ncl:                        0
% 15.62/2.48  bin_hyper_res:                          0
% 15.62/2.48  prep_cycles:                            3
% 15.62/2.48  pred_elim_time:                         0.001
% 15.62/2.48  splitting_time:                         0.
% 15.62/2.48  sem_filter_time:                        0.
% 15.62/2.48  monotx_time:                            0.
% 15.62/2.48  subtype_inf_time:                       0.
% 15.62/2.48  
% 15.62/2.48  ------ Problem properties
% 15.62/2.48  
% 15.62/2.48  clauses:                                16
% 15.62/2.48  conjectures:                            2
% 15.62/2.48  epr:                                    0
% 15.62/2.48  horn:                                   14
% 15.62/2.48  ground:                                 2
% 15.62/2.48  unary:                                  13
% 15.62/2.48  binary:                                 3
% 15.62/2.48  lits:                                   19
% 15.62/2.48  lits_eq:                                11
% 15.62/2.48  fd_pure:                                0
% 15.62/2.48  fd_pseudo:                              0
% 15.62/2.48  fd_cond:                                1
% 15.62/2.48  fd_pseudo_cond:                         0
% 15.62/2.48  ac_symbols:                             0
% 15.62/2.48  
% 15.62/2.48  ------ Propositional Solver
% 15.62/2.48  
% 15.62/2.48  prop_solver_calls:                      30
% 15.62/2.48  prop_fast_solver_calls:                 454
% 15.62/2.48  smt_solver_calls:                       0
% 15.62/2.48  smt_fast_solver_calls:                  0
% 15.62/2.48  prop_num_of_clauses:                    15058
% 15.62/2.48  prop_preprocess_simplified:             10408
% 15.62/2.48  prop_fo_subsumed:                       0
% 15.62/2.48  prop_solver_time:                       0.
% 15.62/2.48  smt_solver_time:                        0.
% 15.62/2.48  smt_fast_solver_time:                   0.
% 15.62/2.48  prop_fast_solver_time:                  0.
% 15.62/2.48  prop_unsat_core_time:                   0.001
% 15.62/2.48  
% 15.62/2.48  ------ QBF
% 15.62/2.48  
% 15.62/2.48  qbf_q_res:                              0
% 15.62/2.48  qbf_num_tautologies:                    0
% 15.62/2.48  qbf_prep_cycles:                        0
% 15.62/2.48  
% 15.62/2.48  ------ BMC1
% 15.62/2.48  
% 15.62/2.48  bmc1_current_bound:                     -1
% 15.62/2.48  bmc1_last_solved_bound:                 -1
% 15.62/2.48  bmc1_unsat_core_size:                   -1
% 15.62/2.48  bmc1_unsat_core_parents_size:           -1
% 15.62/2.48  bmc1_merge_next_fun:                    0
% 15.62/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.62/2.48  
% 15.62/2.48  ------ Instantiation
% 15.62/2.48  
% 15.62/2.48  inst_num_of_clauses:                    2073
% 15.62/2.48  inst_num_in_passive:                    574
% 15.62/2.48  inst_num_in_active:                     771
% 15.62/2.48  inst_num_in_unprocessed:                728
% 15.62/2.48  inst_num_of_loops:                      1010
% 15.62/2.48  inst_num_of_learning_restarts:          0
% 15.62/2.48  inst_num_moves_active_passive:          233
% 15.62/2.48  inst_lit_activity:                      0
% 15.62/2.48  inst_lit_activity_moves:                0
% 15.62/2.48  inst_num_tautologies:                   0
% 15.62/2.48  inst_num_prop_implied:                  0
% 15.62/2.48  inst_num_existing_simplified:           0
% 15.62/2.48  inst_num_eq_res_simplified:             0
% 15.62/2.48  inst_num_child_elim:                    0
% 15.62/2.48  inst_num_of_dismatching_blockings:      1272
% 15.62/2.48  inst_num_of_non_proper_insts:           2187
% 15.62/2.48  inst_num_of_duplicates:                 0
% 15.62/2.48  inst_inst_num_from_inst_to_res:         0
% 15.62/2.48  inst_dismatching_checking_time:         0.
% 15.62/2.48  
% 15.62/2.48  ------ Resolution
% 15.62/2.48  
% 15.62/2.48  res_num_of_clauses:                     0
% 15.62/2.48  res_num_in_passive:                     0
% 15.62/2.48  res_num_in_active:                      0
% 15.62/2.48  res_num_of_loops:                       64
% 15.62/2.48  res_forward_subset_subsumed:            479
% 15.62/2.48  res_backward_subset_subsumed:           0
% 15.62/2.48  res_forward_subsumed:                   0
% 15.62/2.48  res_backward_subsumed:                  0
% 15.62/2.48  res_forward_subsumption_resolution:     0
% 15.62/2.48  res_backward_subsumption_resolution:    0
% 15.62/2.48  res_clause_to_clause_subsumption:       184418
% 15.62/2.48  res_orphan_elimination:                 0
% 15.62/2.48  res_tautology_del:                      176
% 15.62/2.48  res_num_eq_res_simplified:              0
% 15.62/2.48  res_num_sel_changes:                    0
% 15.62/2.48  res_moves_from_active_to_pass:          0
% 15.62/2.48  
% 15.62/2.48  ------ Superposition
% 15.62/2.48  
% 15.62/2.48  sup_time_total:                         0.
% 15.62/2.48  sup_time_generating:                    0.
% 15.62/2.48  sup_time_sim_full:                      0.
% 15.62/2.48  sup_time_sim_immed:                     0.
% 15.62/2.48  
% 15.62/2.48  sup_num_of_clauses:                     4644
% 15.62/2.48  sup_num_in_active:                      182
% 15.62/2.48  sup_num_in_passive:                     4462
% 15.62/2.48  sup_num_of_loops:                       200
% 15.62/2.48  sup_fw_superposition:                   19019
% 15.62/2.48  sup_bw_superposition:                   17398
% 15.62/2.48  sup_immediate_simplified:               16052
% 15.62/2.48  sup_given_eliminated:                   5
% 15.62/2.48  comparisons_done:                       0
% 15.62/2.48  comparisons_avoided:                    0
% 15.62/2.48  
% 15.62/2.48  ------ Simplifications
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  sim_fw_subset_subsumed:                 28
% 15.62/2.48  sim_bw_subset_subsumed:                 0
% 15.62/2.48  sim_fw_subsumed:                        3797
% 15.62/2.48  sim_bw_subsumed:                        55
% 15.62/2.48  sim_fw_subsumption_res:                 0
% 15.62/2.48  sim_bw_subsumption_res:                 0
% 15.62/2.48  sim_tautology_del:                      2
% 15.62/2.48  sim_eq_tautology_del:                   5171
% 15.62/2.48  sim_eq_res_simp:                        0
% 15.62/2.48  sim_fw_demodulated:                     13526
% 15.62/2.48  sim_bw_demodulated:                     207
% 15.62/2.48  sim_light_normalised:                   5587
% 15.62/2.48  sim_joinable_taut:                      0
% 15.62/2.48  sim_joinable_simp:                      0
% 15.62/2.48  sim_ac_normalised:                      0
% 15.62/2.48  sim_smt_subsumption:                    0
% 15.62/2.48  
%------------------------------------------------------------------------------
