%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:12 EST 2020

% Result     : Theorem 43.50s
% Output     : CNFRefutation 43.50s
% Verified   : 
% Statistics : Number of formulae       :  175 (8835 expanded)
%              Number of clauses        :  139 (2553 expanded)
%              Number of leaves         :   11 (2587 expanded)
%              Depth                    :   43
%              Number of atoms          :  213 (9124 expanded)
%              Number of equality atoms :  170 (8746 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f29,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f30,f23,f23])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_302,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_307,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1654,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_302,c_307])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1783,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1654,c_5])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1788,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_1783,c_4])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_309,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_695,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_309,c_2])).

cnf(c_696,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_695,c_4])).

cnf(c_886,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_696])).

cnf(c_1372,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))) ),
    inference(superposition,[status(thm)],[c_886,c_886])).

cnf(c_1380,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X2))) ),
    inference(superposition,[status(thm)],[c_886,c_7])).

cnf(c_1383,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_1380,c_7])).

cnf(c_1393,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1372,c_1383])).

cnf(c_1394,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1393,c_5])).

cnf(c_1395,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1394,c_5,c_6])).

cnf(c_1487,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_1395,c_7])).

cnf(c_1492,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1487,c_7])).

cnf(c_842,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_785,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_1032,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_785])).

cnf(c_15813,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_842,c_1032])).

cnf(c_2340,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_886,c_842])).

cnf(c_2424,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2340,c_5])).

cnf(c_880,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_8797,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2424,c_880])).

cnf(c_2716,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_2424])).

cnf(c_2748,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2716,c_5])).

cnf(c_8799,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2748,c_880])).

cnf(c_2376,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
    inference(superposition,[status(thm)],[c_842,c_7])).

cnf(c_6188,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_2748,c_7])).

cnf(c_2726,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_2424,c_7])).

cnf(c_6210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_6188,c_6,c_2726])).

cnf(c_8927,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(demodulation,[status(thm)],[c_8799,c_6,c_2376,c_6210])).

cnf(c_8929,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(demodulation,[status(thm)],[c_8797,c_8927])).

cnf(c_15990,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_15813,c_5,c_8929])).

cnf(c_16760,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_15990,c_842])).

cnf(c_16917,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_16760,c_5,c_6,c_6210])).

cnf(c_883,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_890,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_883,c_7])).

cnf(c_17134,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_16917,c_890])).

cnf(c_26321,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1492,c_17134])).

cnf(c_26506,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_26321,c_890])).

cnf(c_26789,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_26506,c_309])).

cnf(c_26790,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_26789,c_4])).

cnf(c_27219,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_26790,c_890])).

cnf(c_27524,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_27219,c_4,c_309])).

cnf(c_33607,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_27524])).

cnf(c_39363,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_1788,c_33607])).

cnf(c_41437,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_39363,c_27524])).

cnf(c_41593,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK0)))),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK0)) ),
    inference(superposition,[status(thm)],[c_6,c_41437])).

cnf(c_27196,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
    inference(superposition,[status(thm)],[c_26790,c_7])).

cnf(c_27558,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_27196,c_7])).

cnf(c_27559,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_27558,c_6])).

cnf(c_41870,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK0)))),sK1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_41593,c_6,c_27559])).

cnf(c_851,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_862,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
    inference(demodulation,[status(thm)],[c_851,c_6])).

cnf(c_5901,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
    inference(demodulation,[status(thm)],[c_862,c_890])).

cnf(c_6022,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))),X4))) ),
    inference(superposition,[status(thm)],[c_5901,c_7])).

cnf(c_6111,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))),X4))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))))) ),
    inference(demodulation,[status(thm)],[c_6022,c_7])).

cnf(c_6016,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3)) ),
    inference(superposition,[status(thm)],[c_5901,c_5])).

cnf(c_6291,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_6016,c_5])).

cnf(c_41871,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,sK1))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_41870,c_6111,c_6291])).

cnf(c_41872,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_41871,c_1788])).

cnf(c_42268,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) ),
    inference(superposition,[status(thm)],[c_41872,c_2424])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_308,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1665,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_308])).

cnf(c_1674,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1665,c_6,c_890])).

cnf(c_152129,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_42268,c_1674])).

cnf(c_42281,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))) ),
    inference(superposition,[status(thm)],[c_41872,c_5])).

cnf(c_45990,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),X0) ),
    inference(superposition,[status(thm)],[c_42281,c_26790])).

cnf(c_47114,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45990,c_6,c_309,c_27524])).

cnf(c_152723,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152129,c_6,c_47114])).

cnf(c_152724,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_152723])).

cnf(c_152725,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152724,c_842])).

cnf(c_152726,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152725,c_6])).

cnf(c_1881,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_1788,c_7])).

cnf(c_694,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_697,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_694,c_309])).

cnf(c_1882,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1881,c_309,c_697,c_880])).

cnf(c_2001,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK1)))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_1882])).

cnf(c_2265,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_309,c_2001])).

cnf(c_2303,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2265,c_4,c_309])).

cnf(c_2014,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,sK1))) ),
    inference(superposition,[status(thm)],[c_1882,c_7])).

cnf(c_2017,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2014,c_7])).

cnf(c_2304,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = sK0 ),
    inference(demodulation,[status(thm)],[c_2303,c_4,c_2017])).

cnf(c_2547,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2304,c_7])).

cnf(c_2561,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_2547,c_4,c_309,c_880])).

cnf(c_5064,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_2561,c_842])).

cnf(c_5093,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_5064,c_5])).

cnf(c_8823,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(sK0,X0),X2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X2)) ),
    inference(superposition,[status(thm)],[c_5093,c_880])).

cnf(c_7014,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK1)),X1)) ),
    inference(superposition,[status(thm)],[c_5093,c_7])).

cnf(c_2343,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK0,X0),sK1) ),
    inference(superposition,[status(thm)],[c_1882,c_842])).

cnf(c_2419,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_2343,c_5])).

cnf(c_2604,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_2419,c_7])).

cnf(c_1878,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1788,c_7])).

cnf(c_1886,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1878,c_785])).

cnf(c_1983,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1886,c_7])).

cnf(c_1985,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1983,c_4,c_309,c_880])).

cnf(c_2789,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1985,c_842])).

cnf(c_2799,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_2789,c_5])).

cnf(c_7051,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK1)),X2)) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7014,c_2604,c_2799])).

cnf(c_7052,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,X2)))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_7051,c_6])).

cnf(c_8902,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_8823,c_6,c_2376,c_7052])).

cnf(c_884,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_888,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_884,c_6])).

cnf(c_889,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_888,c_6,c_7])).

cnf(c_12266,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK0,X2),X3)))))) ),
    inference(superposition,[status(thm)],[c_8902,c_889])).

cnf(c_9393,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_8902,c_842])).

cnf(c_9471,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_9393,c_5,c_6,c_6210])).

cnf(c_12489,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_9471,c_890])).

cnf(c_12296,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X5))))))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))))) ),
    inference(superposition,[status(thm)],[c_889,c_889])).

cnf(c_12569,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3))))) ),
    inference(superposition,[status(thm)],[c_890,c_7])).

cnf(c_12734,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_12569,c_7])).

cnf(c_12912,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X5))))))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) ),
    inference(demodulation,[status(thm)],[c_12296,c_12734])).

cnf(c_12298,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
    inference(superposition,[status(thm)],[c_889,c_842])).

cnf(c_12435,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_12298,c_5])).

cnf(c_12913,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) ),
    inference(demodulation,[status(thm)],[c_12912,c_5,c_12435])).

cnf(c_12956,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X2)))))) ),
    inference(demodulation,[status(thm)],[c_12266,c_12489,c_12913])).

cnf(c_12957,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_12956,c_12435])).

cnf(c_152727,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152726,c_6111,c_12957])).

cnf(c_152728,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_152727,c_309])).

cnf(c_152729,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152728,c_4])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_306,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1584,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_306])).

cnf(c_106104,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1584])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_303,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_110134,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_106104,c_303])).

cnf(c_153457,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_152729,c_110134])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 43.50/5.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.50/5.99  
% 43.50/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.50/5.99  
% 43.50/5.99  ------  iProver source info
% 43.50/5.99  
% 43.50/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.50/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.50/5.99  git: non_committed_changes: false
% 43.50/5.99  git: last_make_outside_of_git: false
% 43.50/5.99  
% 43.50/5.99  ------ 
% 43.50/5.99  
% 43.50/5.99  ------ Input Options
% 43.50/5.99  
% 43.50/5.99  --out_options                           all
% 43.50/5.99  --tptp_safe_out                         true
% 43.50/5.99  --problem_path                          ""
% 43.50/5.99  --include_path                          ""
% 43.50/5.99  --clausifier                            res/vclausify_rel
% 43.50/5.99  --clausifier_options                    ""
% 43.50/5.99  --stdin                                 false
% 43.50/5.99  --stats_out                             all
% 43.50/5.99  
% 43.50/5.99  ------ General Options
% 43.50/5.99  
% 43.50/5.99  --fof                                   false
% 43.50/5.99  --time_out_real                         305.
% 43.50/5.99  --time_out_virtual                      -1.
% 43.50/5.99  --symbol_type_check                     false
% 43.50/5.99  --clausify_out                          false
% 43.50/5.99  --sig_cnt_out                           false
% 43.50/5.99  --trig_cnt_out                          false
% 43.50/5.99  --trig_cnt_out_tolerance                1.
% 43.50/5.99  --trig_cnt_out_sk_spl                   false
% 43.50/5.99  --abstr_cl_out                          false
% 43.50/5.99  
% 43.50/5.99  ------ Global Options
% 43.50/5.99  
% 43.50/5.99  --schedule                              default
% 43.50/5.99  --add_important_lit                     false
% 43.50/5.99  --prop_solver_per_cl                    1000
% 43.50/5.99  --min_unsat_core                        false
% 43.50/5.99  --soft_assumptions                      false
% 43.50/5.99  --soft_lemma_size                       3
% 43.50/5.99  --prop_impl_unit_size                   0
% 43.50/5.99  --prop_impl_unit                        []
% 43.50/5.99  --share_sel_clauses                     true
% 43.50/5.99  --reset_solvers                         false
% 43.50/5.99  --bc_imp_inh                            [conj_cone]
% 43.50/5.99  --conj_cone_tolerance                   3.
% 43.50/5.99  --extra_neg_conj                        none
% 43.50/5.99  --large_theory_mode                     true
% 43.50/5.99  --prolific_symb_bound                   200
% 43.50/5.99  --lt_threshold                          2000
% 43.50/5.99  --clause_weak_htbl                      true
% 43.50/5.99  --gc_record_bc_elim                     false
% 43.50/5.99  
% 43.50/5.99  ------ Preprocessing Options
% 43.50/5.99  
% 43.50/5.99  --preprocessing_flag                    true
% 43.50/5.99  --time_out_prep_mult                    0.1
% 43.50/5.99  --splitting_mode                        input
% 43.50/5.99  --splitting_grd                         true
% 43.50/5.99  --splitting_cvd                         false
% 43.50/5.99  --splitting_cvd_svl                     false
% 43.50/5.99  --splitting_nvd                         32
% 43.50/5.99  --sub_typing                            true
% 43.50/5.99  --prep_gs_sim                           true
% 43.50/5.99  --prep_unflatten                        true
% 43.50/5.99  --prep_res_sim                          true
% 43.50/5.99  --prep_upred                            true
% 43.50/5.99  --prep_sem_filter                       exhaustive
% 43.50/5.99  --prep_sem_filter_out                   false
% 43.50/5.99  --pred_elim                             true
% 43.50/5.99  --res_sim_input                         true
% 43.50/5.99  --eq_ax_congr_red                       true
% 43.50/5.99  --pure_diseq_elim                       true
% 43.50/5.99  --brand_transform                       false
% 43.50/5.99  --non_eq_to_eq                          false
% 43.50/5.99  --prep_def_merge                        true
% 43.50/5.99  --prep_def_merge_prop_impl              false
% 43.50/5.99  --prep_def_merge_mbd                    true
% 43.50/5.99  --prep_def_merge_tr_red                 false
% 43.50/5.99  --prep_def_merge_tr_cl                  false
% 43.50/5.99  --smt_preprocessing                     true
% 43.50/5.99  --smt_ac_axioms                         fast
% 43.50/5.99  --preprocessed_out                      false
% 43.50/5.99  --preprocessed_stats                    false
% 43.50/5.99  
% 43.50/5.99  ------ Abstraction refinement Options
% 43.50/5.99  
% 43.50/5.99  --abstr_ref                             []
% 43.50/5.99  --abstr_ref_prep                        false
% 43.50/5.99  --abstr_ref_until_sat                   false
% 43.50/5.99  --abstr_ref_sig_restrict                funpre
% 43.50/5.99  --abstr_ref_af_restrict_to_split_sk     false
% 43.50/5.99  --abstr_ref_under                       []
% 43.50/5.99  
% 43.50/5.99  ------ SAT Options
% 43.50/5.99  
% 43.50/5.99  --sat_mode                              false
% 43.50/5.99  --sat_fm_restart_options                ""
% 43.50/5.99  --sat_gr_def                            false
% 43.50/5.99  --sat_epr_types                         true
% 43.50/5.99  --sat_non_cyclic_types                  false
% 43.50/5.99  --sat_finite_models                     false
% 43.50/5.99  --sat_fm_lemmas                         false
% 43.50/5.99  --sat_fm_prep                           false
% 43.50/5.99  --sat_fm_uc_incr                        true
% 43.50/5.99  --sat_out_model                         small
% 43.50/5.99  --sat_out_clauses                       false
% 43.50/5.99  
% 43.50/5.99  ------ QBF Options
% 43.50/5.99  
% 43.50/5.99  --qbf_mode                              false
% 43.50/5.99  --qbf_elim_univ                         false
% 43.50/5.99  --qbf_dom_inst                          none
% 43.50/5.99  --qbf_dom_pre_inst                      false
% 43.50/5.99  --qbf_sk_in                             false
% 43.50/5.99  --qbf_pred_elim                         true
% 43.50/5.99  --qbf_split                             512
% 43.50/5.99  
% 43.50/5.99  ------ BMC1 Options
% 43.50/5.99  
% 43.50/5.99  --bmc1_incremental                      false
% 43.50/5.99  --bmc1_axioms                           reachable_all
% 43.50/5.99  --bmc1_min_bound                        0
% 43.50/5.99  --bmc1_max_bound                        -1
% 43.50/5.99  --bmc1_max_bound_default                -1
% 43.50/5.99  --bmc1_symbol_reachability              true
% 43.50/5.99  --bmc1_property_lemmas                  false
% 43.50/5.99  --bmc1_k_induction                      false
% 43.50/5.99  --bmc1_non_equiv_states                 false
% 43.50/5.99  --bmc1_deadlock                         false
% 43.50/5.99  --bmc1_ucm                              false
% 43.50/5.99  --bmc1_add_unsat_core                   none
% 43.50/5.99  --bmc1_unsat_core_children              false
% 43.50/5.99  --bmc1_unsat_core_extrapolate_axioms    false
% 43.50/5.99  --bmc1_out_stat                         full
% 43.50/5.99  --bmc1_ground_init                      false
% 43.50/5.99  --bmc1_pre_inst_next_state              false
% 43.50/5.99  --bmc1_pre_inst_state                   false
% 43.50/5.99  --bmc1_pre_inst_reach_state             false
% 43.50/5.99  --bmc1_out_unsat_core                   false
% 43.50/5.99  --bmc1_aig_witness_out                  false
% 43.50/5.99  --bmc1_verbose                          false
% 43.50/5.99  --bmc1_dump_clauses_tptp                false
% 43.50/5.99  --bmc1_dump_unsat_core_tptp             false
% 43.50/5.99  --bmc1_dump_file                        -
% 43.50/5.99  --bmc1_ucm_expand_uc_limit              128
% 43.50/5.99  --bmc1_ucm_n_expand_iterations          6
% 43.50/5.99  --bmc1_ucm_extend_mode                  1
% 43.50/5.99  --bmc1_ucm_init_mode                    2
% 43.50/5.99  --bmc1_ucm_cone_mode                    none
% 43.50/5.99  --bmc1_ucm_reduced_relation_type        0
% 43.50/5.99  --bmc1_ucm_relax_model                  4
% 43.50/5.99  --bmc1_ucm_full_tr_after_sat            true
% 43.50/5.99  --bmc1_ucm_expand_neg_assumptions       false
% 43.50/5.99  --bmc1_ucm_layered_model                none
% 43.50/5.99  --bmc1_ucm_max_lemma_size               10
% 43.50/5.99  
% 43.50/5.99  ------ AIG Options
% 43.50/5.99  
% 43.50/5.99  --aig_mode                              false
% 43.50/5.99  
% 43.50/5.99  ------ Instantiation Options
% 43.50/5.99  
% 43.50/5.99  --instantiation_flag                    true
% 43.50/5.99  --inst_sos_flag                         true
% 43.50/5.99  --inst_sos_phase                        true
% 43.50/5.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.50/5.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.50/5.99  --inst_lit_sel_side                     num_symb
% 43.50/5.99  --inst_solver_per_active                1400
% 43.50/5.99  --inst_solver_calls_frac                1.
% 43.50/5.99  --inst_passive_queue_type               priority_queues
% 43.50/5.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.50/5.99  --inst_passive_queues_freq              [25;2]
% 43.50/5.99  --inst_dismatching                      true
% 43.50/5.99  --inst_eager_unprocessed_to_passive     true
% 43.50/5.99  --inst_prop_sim_given                   true
% 43.50/5.99  --inst_prop_sim_new                     false
% 43.50/5.99  --inst_subs_new                         false
% 43.50/5.99  --inst_eq_res_simp                      false
% 43.50/5.99  --inst_subs_given                       false
% 43.50/5.99  --inst_orphan_elimination               true
% 43.50/5.99  --inst_learning_loop_flag               true
% 43.50/5.99  --inst_learning_start                   3000
% 43.50/5.99  --inst_learning_factor                  2
% 43.50/5.99  --inst_start_prop_sim_after_learn       3
% 43.50/5.99  --inst_sel_renew                        solver
% 43.50/5.99  --inst_lit_activity_flag                true
% 43.50/5.99  --inst_restr_to_given                   false
% 43.50/5.99  --inst_activity_threshold               500
% 43.50/5.99  --inst_out_proof                        true
% 43.50/5.99  
% 43.50/5.99  ------ Resolution Options
% 43.50/5.99  
% 43.50/5.99  --resolution_flag                       true
% 43.50/5.99  --res_lit_sel                           adaptive
% 43.50/5.99  --res_lit_sel_side                      none
% 43.50/5.99  --res_ordering                          kbo
% 43.50/5.99  --res_to_prop_solver                    active
% 43.50/5.99  --res_prop_simpl_new                    false
% 43.50/5.99  --res_prop_simpl_given                  true
% 43.50/5.99  --res_passive_queue_type                priority_queues
% 43.50/5.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.50/5.99  --res_passive_queues_freq               [15;5]
% 43.50/5.99  --res_forward_subs                      full
% 43.50/5.99  --res_backward_subs                     full
% 43.50/5.99  --res_forward_subs_resolution           true
% 43.50/5.99  --res_backward_subs_resolution          true
% 43.50/5.99  --res_orphan_elimination                true
% 43.50/5.99  --res_time_limit                        2.
% 43.50/5.99  --res_out_proof                         true
% 43.50/5.99  
% 43.50/5.99  ------ Superposition Options
% 43.50/5.99  
% 43.50/5.99  --superposition_flag                    true
% 43.50/5.99  --sup_passive_queue_type                priority_queues
% 43.50/5.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.50/5.99  --sup_passive_queues_freq               [8;1;4]
% 43.50/5.99  --demod_completeness_check              fast
% 43.50/5.99  --demod_use_ground                      true
% 43.50/5.99  --sup_to_prop_solver                    passive
% 43.50/5.99  --sup_prop_simpl_new                    true
% 43.50/5.99  --sup_prop_simpl_given                  true
% 43.50/5.99  --sup_fun_splitting                     true
% 43.50/5.99  --sup_smt_interval                      50000
% 43.50/5.99  
% 43.50/5.99  ------ Superposition Simplification Setup
% 43.50/5.99  
% 43.50/5.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.50/5.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.50/5.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.50/5.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.50/5.99  --sup_full_triv                         [TrivRules;PropSubs]
% 43.50/5.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.50/5.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.50/5.99  --sup_immed_triv                        [TrivRules]
% 43.50/5.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/5.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/5.99  --sup_immed_bw_main                     []
% 43.50/5.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.50/5.99  --sup_input_triv                        [Unflattening;TrivRules]
% 43.50/5.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/5.99  --sup_input_bw                          []
% 43.50/5.99  
% 43.50/5.99  ------ Combination Options
% 43.50/5.99  
% 43.50/5.99  --comb_res_mult                         3
% 43.50/5.99  --comb_sup_mult                         2
% 43.50/5.99  --comb_inst_mult                        10
% 43.50/5.99  
% 43.50/5.99  ------ Debug Options
% 43.50/5.99  
% 43.50/5.99  --dbg_backtrace                         false
% 43.50/5.99  --dbg_dump_prop_clauses                 false
% 43.50/5.99  --dbg_dump_prop_clauses_file            -
% 43.50/5.99  --dbg_out_stat                          false
% 43.50/5.99  ------ Parsing...
% 43.50/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.50/5.99  
% 43.50/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.50/5.99  
% 43.50/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.50/5.99  
% 43.50/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.50/5.99  ------ Proving...
% 43.50/5.99  ------ Problem Properties 
% 43.50/5.99  
% 43.50/5.99  
% 43.50/5.99  clauses                                 13
% 43.50/5.99  conjectures                             2
% 43.50/5.99  EPR                                     1
% 43.50/5.99  Horn                                    13
% 43.50/5.99  unary                                   8
% 43.50/5.99  binary                                  4
% 43.50/5.99  lits                                    19
% 43.50/5.99  lits eq                                 8
% 43.50/5.99  fd_pure                                 0
% 43.50/5.99  fd_pseudo                               0
% 43.50/5.99  fd_cond                                 0
% 43.50/5.99  fd_pseudo_cond                          0
% 43.50/5.99  AC symbols                              0
% 43.50/5.99  
% 43.50/5.99  ------ Schedule dynamic 5 is on 
% 43.50/5.99  
% 43.50/5.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.50/5.99  
% 43.50/5.99  
% 43.50/5.99  ------ 
% 43.50/5.99  Current options:
% 43.50/5.99  ------ 
% 43.50/5.99  
% 43.50/5.99  ------ Input Options
% 43.50/5.99  
% 43.50/5.99  --out_options                           all
% 43.50/5.99  --tptp_safe_out                         true
% 43.50/5.99  --problem_path                          ""
% 43.50/5.99  --include_path                          ""
% 43.50/5.99  --clausifier                            res/vclausify_rel
% 43.50/5.99  --clausifier_options                    ""
% 43.50/5.99  --stdin                                 false
% 43.50/5.99  --stats_out                             all
% 43.50/5.99  
% 43.50/5.99  ------ General Options
% 43.50/5.99  
% 43.50/5.99  --fof                                   false
% 43.50/5.99  --time_out_real                         305.
% 43.50/5.99  --time_out_virtual                      -1.
% 43.50/5.99  --symbol_type_check                     false
% 43.50/5.99  --clausify_out                          false
% 43.50/5.99  --sig_cnt_out                           false
% 43.50/5.99  --trig_cnt_out                          false
% 43.50/5.99  --trig_cnt_out_tolerance                1.
% 43.50/5.99  --trig_cnt_out_sk_spl                   false
% 43.50/5.99  --abstr_cl_out                          false
% 43.50/5.99  
% 43.50/5.99  ------ Global Options
% 43.50/5.99  
% 43.50/5.99  --schedule                              default
% 43.50/5.99  --add_important_lit                     false
% 43.50/5.99  --prop_solver_per_cl                    1000
% 43.50/5.99  --min_unsat_core                        false
% 43.50/5.99  --soft_assumptions                      false
% 43.50/5.99  --soft_lemma_size                       3
% 43.50/5.99  --prop_impl_unit_size                   0
% 43.50/5.99  --prop_impl_unit                        []
% 43.50/5.99  --share_sel_clauses                     true
% 43.50/5.99  --reset_solvers                         false
% 43.50/5.99  --bc_imp_inh                            [conj_cone]
% 43.50/5.99  --conj_cone_tolerance                   3.
% 43.50/5.99  --extra_neg_conj                        none
% 43.50/5.99  --large_theory_mode                     true
% 43.50/5.99  --prolific_symb_bound                   200
% 43.50/5.99  --lt_threshold                          2000
% 43.50/6.00  --clause_weak_htbl                      true
% 43.50/6.00  --gc_record_bc_elim                     false
% 43.50/6.00  
% 43.50/6.00  ------ Preprocessing Options
% 43.50/6.00  
% 43.50/6.00  --preprocessing_flag                    true
% 43.50/6.00  --time_out_prep_mult                    0.1
% 43.50/6.00  --splitting_mode                        input
% 43.50/6.00  --splitting_grd                         true
% 43.50/6.00  --splitting_cvd                         false
% 43.50/6.00  --splitting_cvd_svl                     false
% 43.50/6.00  --splitting_nvd                         32
% 43.50/6.00  --sub_typing                            true
% 43.50/6.00  --prep_gs_sim                           true
% 43.50/6.00  --prep_unflatten                        true
% 43.50/6.00  --prep_res_sim                          true
% 43.50/6.00  --prep_upred                            true
% 43.50/6.00  --prep_sem_filter                       exhaustive
% 43.50/6.00  --prep_sem_filter_out                   false
% 43.50/6.00  --pred_elim                             true
% 43.50/6.00  --res_sim_input                         true
% 43.50/6.00  --eq_ax_congr_red                       true
% 43.50/6.00  --pure_diseq_elim                       true
% 43.50/6.00  --brand_transform                       false
% 43.50/6.00  --non_eq_to_eq                          false
% 43.50/6.00  --prep_def_merge                        true
% 43.50/6.00  --prep_def_merge_prop_impl              false
% 43.50/6.00  --prep_def_merge_mbd                    true
% 43.50/6.00  --prep_def_merge_tr_red                 false
% 43.50/6.00  --prep_def_merge_tr_cl                  false
% 43.50/6.00  --smt_preprocessing                     true
% 43.50/6.00  --smt_ac_axioms                         fast
% 43.50/6.00  --preprocessed_out                      false
% 43.50/6.00  --preprocessed_stats                    false
% 43.50/6.00  
% 43.50/6.00  ------ Abstraction refinement Options
% 43.50/6.00  
% 43.50/6.00  --abstr_ref                             []
% 43.50/6.00  --abstr_ref_prep                        false
% 43.50/6.00  --abstr_ref_until_sat                   false
% 43.50/6.00  --abstr_ref_sig_restrict                funpre
% 43.50/6.00  --abstr_ref_af_restrict_to_split_sk     false
% 43.50/6.00  --abstr_ref_under                       []
% 43.50/6.00  
% 43.50/6.00  ------ SAT Options
% 43.50/6.00  
% 43.50/6.00  --sat_mode                              false
% 43.50/6.00  --sat_fm_restart_options                ""
% 43.50/6.00  --sat_gr_def                            false
% 43.50/6.00  --sat_epr_types                         true
% 43.50/6.00  --sat_non_cyclic_types                  false
% 43.50/6.00  --sat_finite_models                     false
% 43.50/6.00  --sat_fm_lemmas                         false
% 43.50/6.00  --sat_fm_prep                           false
% 43.50/6.00  --sat_fm_uc_incr                        true
% 43.50/6.00  --sat_out_model                         small
% 43.50/6.00  --sat_out_clauses                       false
% 43.50/6.00  
% 43.50/6.00  ------ QBF Options
% 43.50/6.00  
% 43.50/6.00  --qbf_mode                              false
% 43.50/6.00  --qbf_elim_univ                         false
% 43.50/6.00  --qbf_dom_inst                          none
% 43.50/6.00  --qbf_dom_pre_inst                      false
% 43.50/6.00  --qbf_sk_in                             false
% 43.50/6.00  --qbf_pred_elim                         true
% 43.50/6.00  --qbf_split                             512
% 43.50/6.00  
% 43.50/6.00  ------ BMC1 Options
% 43.50/6.00  
% 43.50/6.00  --bmc1_incremental                      false
% 43.50/6.00  --bmc1_axioms                           reachable_all
% 43.50/6.00  --bmc1_min_bound                        0
% 43.50/6.00  --bmc1_max_bound                        -1
% 43.50/6.00  --bmc1_max_bound_default                -1
% 43.50/6.00  --bmc1_symbol_reachability              true
% 43.50/6.00  --bmc1_property_lemmas                  false
% 43.50/6.00  --bmc1_k_induction                      false
% 43.50/6.00  --bmc1_non_equiv_states                 false
% 43.50/6.00  --bmc1_deadlock                         false
% 43.50/6.00  --bmc1_ucm                              false
% 43.50/6.00  --bmc1_add_unsat_core                   none
% 43.50/6.00  --bmc1_unsat_core_children              false
% 43.50/6.00  --bmc1_unsat_core_extrapolate_axioms    false
% 43.50/6.00  --bmc1_out_stat                         full
% 43.50/6.00  --bmc1_ground_init                      false
% 43.50/6.00  --bmc1_pre_inst_next_state              false
% 43.50/6.00  --bmc1_pre_inst_state                   false
% 43.50/6.00  --bmc1_pre_inst_reach_state             false
% 43.50/6.00  --bmc1_out_unsat_core                   false
% 43.50/6.00  --bmc1_aig_witness_out                  false
% 43.50/6.00  --bmc1_verbose                          false
% 43.50/6.00  --bmc1_dump_clauses_tptp                false
% 43.50/6.00  --bmc1_dump_unsat_core_tptp             false
% 43.50/6.00  --bmc1_dump_file                        -
% 43.50/6.00  --bmc1_ucm_expand_uc_limit              128
% 43.50/6.00  --bmc1_ucm_n_expand_iterations          6
% 43.50/6.00  --bmc1_ucm_extend_mode                  1
% 43.50/6.00  --bmc1_ucm_init_mode                    2
% 43.50/6.00  --bmc1_ucm_cone_mode                    none
% 43.50/6.00  --bmc1_ucm_reduced_relation_type        0
% 43.50/6.00  --bmc1_ucm_relax_model                  4
% 43.50/6.00  --bmc1_ucm_full_tr_after_sat            true
% 43.50/6.00  --bmc1_ucm_expand_neg_assumptions       false
% 43.50/6.00  --bmc1_ucm_layered_model                none
% 43.50/6.00  --bmc1_ucm_max_lemma_size               10
% 43.50/6.00  
% 43.50/6.00  ------ AIG Options
% 43.50/6.00  
% 43.50/6.00  --aig_mode                              false
% 43.50/6.00  
% 43.50/6.00  ------ Instantiation Options
% 43.50/6.00  
% 43.50/6.00  --instantiation_flag                    true
% 43.50/6.00  --inst_sos_flag                         true
% 43.50/6.00  --inst_sos_phase                        true
% 43.50/6.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.50/6.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.50/6.00  --inst_lit_sel_side                     none
% 43.50/6.00  --inst_solver_per_active                1400
% 43.50/6.00  --inst_solver_calls_frac                1.
% 43.50/6.00  --inst_passive_queue_type               priority_queues
% 43.50/6.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.50/6.00  --inst_passive_queues_freq              [25;2]
% 43.50/6.00  --inst_dismatching                      true
% 43.50/6.00  --inst_eager_unprocessed_to_passive     true
% 43.50/6.00  --inst_prop_sim_given                   true
% 43.50/6.00  --inst_prop_sim_new                     false
% 43.50/6.00  --inst_subs_new                         false
% 43.50/6.00  --inst_eq_res_simp                      false
% 43.50/6.00  --inst_subs_given                       false
% 43.50/6.00  --inst_orphan_elimination               true
% 43.50/6.00  --inst_learning_loop_flag               true
% 43.50/6.00  --inst_learning_start                   3000
% 43.50/6.00  --inst_learning_factor                  2
% 43.50/6.00  --inst_start_prop_sim_after_learn       3
% 43.50/6.00  --inst_sel_renew                        solver
% 43.50/6.00  --inst_lit_activity_flag                true
% 43.50/6.00  --inst_restr_to_given                   false
% 43.50/6.00  --inst_activity_threshold               500
% 43.50/6.00  --inst_out_proof                        true
% 43.50/6.00  
% 43.50/6.00  ------ Resolution Options
% 43.50/6.00  
% 43.50/6.00  --resolution_flag                       false
% 43.50/6.00  --res_lit_sel                           adaptive
% 43.50/6.00  --res_lit_sel_side                      none
% 43.50/6.00  --res_ordering                          kbo
% 43.50/6.00  --res_to_prop_solver                    active
% 43.50/6.00  --res_prop_simpl_new                    false
% 43.50/6.00  --res_prop_simpl_given                  true
% 43.50/6.00  --res_passive_queue_type                priority_queues
% 43.50/6.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.50/6.00  --res_passive_queues_freq               [15;5]
% 43.50/6.00  --res_forward_subs                      full
% 43.50/6.00  --res_backward_subs                     full
% 43.50/6.00  --res_forward_subs_resolution           true
% 43.50/6.00  --res_backward_subs_resolution          true
% 43.50/6.00  --res_orphan_elimination                true
% 43.50/6.00  --res_time_limit                        2.
% 43.50/6.00  --res_out_proof                         true
% 43.50/6.00  
% 43.50/6.00  ------ Superposition Options
% 43.50/6.00  
% 43.50/6.00  --superposition_flag                    true
% 43.50/6.00  --sup_passive_queue_type                priority_queues
% 43.50/6.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.50/6.00  --sup_passive_queues_freq               [8;1;4]
% 43.50/6.00  --demod_completeness_check              fast
% 43.50/6.00  --demod_use_ground                      true
% 43.50/6.00  --sup_to_prop_solver                    passive
% 43.50/6.00  --sup_prop_simpl_new                    true
% 43.50/6.00  --sup_prop_simpl_given                  true
% 43.50/6.00  --sup_fun_splitting                     true
% 43.50/6.00  --sup_smt_interval                      50000
% 43.50/6.00  
% 43.50/6.00  ------ Superposition Simplification Setup
% 43.50/6.00  
% 43.50/6.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.50/6.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.50/6.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.50/6.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.50/6.00  --sup_full_triv                         [TrivRules;PropSubs]
% 43.50/6.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.50/6.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.50/6.00  --sup_immed_triv                        [TrivRules]
% 43.50/6.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/6.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/6.00  --sup_immed_bw_main                     []
% 43.50/6.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.50/6.00  --sup_input_triv                        [Unflattening;TrivRules]
% 43.50/6.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.50/6.00  --sup_input_bw                          []
% 43.50/6.00  
% 43.50/6.00  ------ Combination Options
% 43.50/6.00  
% 43.50/6.00  --comb_res_mult                         3
% 43.50/6.00  --comb_sup_mult                         2
% 43.50/6.00  --comb_inst_mult                        10
% 43.50/6.00  
% 43.50/6.00  ------ Debug Options
% 43.50/6.00  
% 43.50/6.00  --dbg_backtrace                         false
% 43.50/6.00  --dbg_dump_prop_clauses                 false
% 43.50/6.00  --dbg_dump_prop_clauses_file            -
% 43.50/6.00  --dbg_out_stat                          false
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  ------ Proving...
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  % SZS status Theorem for theBenchmark.p
% 43.50/6.00  
% 43.50/6.00   Resolution empty clause
% 43.50/6.00  
% 43.50/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.50/6.00  
% 43.50/6.00  fof(f7,axiom,(
% 43.50/6.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f24,plain,(
% 43.50/6.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 43.50/6.00    inference(cnf_transformation,[],[f7])).
% 43.50/6.00  
% 43.50/6.00  fof(f6,axiom,(
% 43.50/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f23,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.50/6.00    inference(cnf_transformation,[],[f6])).
% 43.50/6.00  
% 43.50/6.00  fof(f36,plain,(
% 43.50/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 43.50/6.00    inference(definition_unfolding,[],[f24,f23,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f10,conjecture,(
% 43.50/6.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f11,negated_conjecture,(
% 43.50/6.00    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 43.50/6.00    inference(negated_conjecture,[],[f10])).
% 43.50/6.00  
% 43.50/6.00  fof(f13,plain,(
% 43.50/6.00    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 43.50/6.00    inference(ennf_transformation,[],[f11])).
% 43.50/6.00  
% 43.50/6.00  fof(f15,plain,(
% 43.50/6.00    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 43.50/6.00    introduced(choice_axiom,[])).
% 43.50/6.00  
% 43.50/6.00  fof(f16,plain,(
% 43.50/6.00    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 43.50/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 43.50/6.00  
% 43.50/6.00  fof(f29,plain,(
% 43.50/6.00    r1_xboole_0(sK0,sK1)),
% 43.50/6.00    inference(cnf_transformation,[],[f16])).
% 43.50/6.00  
% 43.50/6.00  fof(f1,axiom,(
% 43.50/6.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f14,plain,(
% 43.50/6.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 43.50/6.00    inference(nnf_transformation,[],[f1])).
% 43.50/6.00  
% 43.50/6.00  fof(f17,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 43.50/6.00    inference(cnf_transformation,[],[f14])).
% 43.50/6.00  
% 43.50/6.00  fof(f32,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 43.50/6.00    inference(definition_unfolding,[],[f17,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f5,axiom,(
% 43.50/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f22,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.50/6.00    inference(cnf_transformation,[],[f5])).
% 43.50/6.00  
% 43.50/6.00  fof(f35,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 43.50/6.00    inference(definition_unfolding,[],[f22,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f4,axiom,(
% 43.50/6.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f21,plain,(
% 43.50/6.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.50/6.00    inference(cnf_transformation,[],[f4])).
% 43.50/6.00  
% 43.50/6.00  fof(f8,axiom,(
% 43.50/6.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f25,plain,(
% 43.50/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 43.50/6.00    inference(cnf_transformation,[],[f8])).
% 43.50/6.00  
% 43.50/6.00  fof(f37,plain,(
% 43.50/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 43.50/6.00    inference(definition_unfolding,[],[f25,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f3,axiom,(
% 43.50/6.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f20,plain,(
% 43.50/6.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 43.50/6.00    inference(cnf_transformation,[],[f3])).
% 43.50/6.00  
% 43.50/6.00  fof(f34,plain,(
% 43.50/6.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 43.50/6.00    inference(definition_unfolding,[],[f20,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f2,axiom,(
% 43.50/6.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f19,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 43.50/6.00    inference(cnf_transformation,[],[f2])).
% 43.50/6.00  
% 43.50/6.00  fof(f33,plain,(
% 43.50/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 43.50/6.00    inference(definition_unfolding,[],[f19,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f18,plain,(
% 43.50/6.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 43.50/6.00    inference(cnf_transformation,[],[f14])).
% 43.50/6.00  
% 43.50/6.00  fof(f31,plain,(
% 43.50/6.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.50/6.00    inference(definition_unfolding,[],[f18,f23])).
% 43.50/6.00  
% 43.50/6.00  fof(f9,axiom,(
% 43.50/6.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 43.50/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.50/6.00  
% 43.50/6.00  fof(f12,plain,(
% 43.50/6.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 43.50/6.00    inference(ennf_transformation,[],[f9])).
% 43.50/6.00  
% 43.50/6.00  fof(f28,plain,(
% 43.50/6.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 43.50/6.00    inference(cnf_transformation,[],[f12])).
% 43.50/6.00  
% 43.50/6.00  fof(f30,plain,(
% 43.50/6.00    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 43.50/6.00    inference(cnf_transformation,[],[f16])).
% 43.50/6.00  
% 43.50/6.00  fof(f38,plain,(
% 43.50/6.00    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 43.50/6.00    inference(definition_unfolding,[],[f30,f23,f23])).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 43.50/6.00      inference(cnf_transformation,[],[f36]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12,negated_conjecture,
% 43.50/6.00      ( r1_xboole_0(sK0,sK1) ),
% 43.50/6.00      inference(cnf_transformation,[],[f29]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_302,plain,
% 43.50/6.00      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 43.50/6.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1,plain,
% 43.50/6.00      ( ~ r1_xboole_0(X0,X1)
% 43.50/6.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 43.50/6.00      inference(cnf_transformation,[],[f32]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_307,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 43.50/6.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 43.50/6.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1654,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_302,c_307]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_5,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(cnf_transformation,[],[f35]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1783,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1654,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_4,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.50/6.00      inference(cnf_transformation,[],[f21]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1788,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1783,c_4]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_7,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(cnf_transformation,[],[f37]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_3,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 43.50/6.00      inference(cnf_transformation,[],[f34]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_309,plain,
% 43.50/6.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2,plain,
% 43.50/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 43.50/6.00      inference(cnf_transformation,[],[f33]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_695,plain,
% 43.50/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_309,c_2]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_696,plain,
% 43.50/6.00      ( k2_xboole_0(X0,X0) = X0 ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_695,c_4]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_886,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_7,c_696]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1372,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_886,c_886]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1380,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X2))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_886,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1383,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1380,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1393,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1372,c_1383]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1394,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_1393,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1395,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X1))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1394,c_5,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1487,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X2)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1395,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1492,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X2),X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_1487,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_842,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_785,plain,
% 43.50/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1032,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_785]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_15813,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_842,c_1032]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2340,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_886,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2424,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_2340,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_880,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8797,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2424,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2716,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5,c_2424]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2748,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_2716,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8799,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2748,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2376,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_842,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6188,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2748,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2726,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2424,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6210,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_6188,c_6,c_2726]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8927,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_8799,c_6,c_2376,c_6210]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8929,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_8797,c_8927]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_15990,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_15813,c_5,c_8929]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_16760,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_15990,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_16917,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_16760,c_5,c_6,c_6210]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_883,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_890,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_883,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_17134,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_16917,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_26321,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1492,c_17134]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_26506,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_26321,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_26789,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_26506,c_309]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_26790,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_26789,c_4]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_27219,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_26790,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_27524,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_27219,c_4,c_309]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_33607,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_27524]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_39363,plain,
% 43.50/6.00      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = sK1 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1788,c_33607]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_41437,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),sK1) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_39363,c_27524]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_41593,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK0)))),sK1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_41437]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_27196,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_26790,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_27558,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_27196,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_27559,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_27558,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_41870,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK0)))),sK1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_41593,c_6,c_27559]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_851,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_862,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_851,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_5901,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_862,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6022,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))),X4))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5901,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6111,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))),X4))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_6022,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6016,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5901,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_6291,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_6016,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_41871,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,sK1))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_41870,c_6111,c_6291]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_41872,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_41871,c_1788]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_42268,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0)))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_41872,c_2424]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_0,plain,
% 43.50/6.00      ( r1_xboole_0(X0,X1)
% 43.50/6.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 43.50/6.00      inference(cnf_transformation,[],[f31]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_308,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 43.50/6.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 43.50/6.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1665,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) != k1_xboole_0
% 43.50/6.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = iProver_top ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_308]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1674,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) != k1_xboole_0
% 43.50/6.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1665,c_6,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152129,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0))))) != k1_xboole_0
% 43.50/6.00      | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_42268,c_1674]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_42281,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_41872,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_45990,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),X0) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_42281,c_26790]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_47114,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,sK0)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK0))))) = k1_xboole_0 ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_45990,c_6,c_309,c_27524]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152723,plain,
% 43.50/6.00      ( k1_xboole_0 != k1_xboole_0
% 43.50/6.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_152129,c_6,c_47114]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152724,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(equality_resolution_simp,[status(thm)],[c_152723]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152725,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_152724,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152726,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))),X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_152725,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1881,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1788,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_694,plain,
% 43.50/6.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_697,plain,
% 43.50/6.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_694,c_309]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1882,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1881,c_309,c_697,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2001,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sK1)))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_1882]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2265,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_309,c_2001]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2303,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_2265,c_4,c_309]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2014,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,sK1))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1882,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2017,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_2014,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2304,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = sK0 ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_2303,c_4,c_2017]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2547,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2304,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2561,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_2547,c_4,c_309,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_5064,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2561,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_5093,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_5064,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8823,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK1)),k4_xboole_0(k4_xboole_0(sK0,X0),X2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X2)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5093,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_7014,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK1)),X1)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_5093,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2343,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK0,X0),sK1) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1882,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2419,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_2343,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2604,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_2419,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1878,plain,
% 43.50/6.00      ( k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1788,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1886,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = sK0 ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1878,c_785]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1983,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1886,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1985,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,X1))) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_1983,c_4,c_309,c_880]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2789,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1985,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_2799,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_2789,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_7051,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,sK1)),X2)) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_7014,c_2604,c_2799]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_7052,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,X2)))) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_7051,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8902,plain,
% 43.50/6.00      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,X0),X1))) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_8823,c_6,c_2376,c_7052]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_884,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_888,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3)) ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_884,c_6]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_889,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_888,c_6,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12266,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(sK0,X2),X3)))))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_8902,c_889]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_9393,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_8902,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_9471,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X0,X1)) = k4_xboole_0(sK0,X0) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_9393,c_5,c_6,c_6210]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12489,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,X0),X1)) = k4_xboole_0(X0,k4_xboole_0(sK0,X0)) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_9471,c_890]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12296,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X5))))))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_889,c_889]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12569,plain,
% 43.50/6.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X3)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3))))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_890,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12734,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12569,c_7]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12912,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X5))))))))) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12296,c_12734]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12298,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))) ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_889,c_842]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12435,plain,
% 43.50/6.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12298,c_5]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12913,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12912,c_5,c_12435]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12956,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X2)))))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12266,c_12489,c_12913]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_12957,plain,
% 43.50/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X1,X2)))) ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_12956,c_12435]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152727,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(X0,X0)))),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_152726,c_6111,c_12957]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152728,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(light_normalisation,[status(thm)],[c_152727,c_309]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_152729,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(X0,sK0)) = iProver_top ),
% 43.50/6.00      inference(demodulation,[status(thm)],[c_152728,c_4]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_8,plain,
% 43.50/6.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 43.50/6.00      inference(cnf_transformation,[],[f28]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_306,plain,
% 43.50/6.00      ( r1_xboole_0(X0,X1) = iProver_top
% 43.50/6.00      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 43.50/6.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_1584,plain,
% 43.50/6.00      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) != iProver_top
% 43.50/6.00      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X3))) = iProver_top ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_7,c_306]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_106104,plain,
% 43.50/6.00      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1))) = iProver_top
% 43.50/6.00      | r1_xboole_0(X0,k4_xboole_0(X1,sK0)) != iProver_top ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_1788,c_1584]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_11,negated_conjecture,
% 43.50/6.00      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 43.50/6.00      inference(cnf_transformation,[],[f38]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_303,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) != iProver_top ),
% 43.50/6.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_110134,plain,
% 43.50/6.00      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0)) != iProver_top ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_106104,c_303]) ).
% 43.50/6.00  
% 43.50/6.00  cnf(c_153457,plain,
% 43.50/6.00      ( $false ),
% 43.50/6.00      inference(superposition,[status(thm)],[c_152729,c_110134]) ).
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.50/6.00  
% 43.50/6.00  ------                               Statistics
% 43.50/6.00  
% 43.50/6.00  ------ General
% 43.50/6.00  
% 43.50/6.00  abstr_ref_over_cycles:                  0
% 43.50/6.00  abstr_ref_under_cycles:                 0
% 43.50/6.00  gc_basic_clause_elim:                   0
% 43.50/6.00  forced_gc_time:                         0
% 43.50/6.00  parsing_time:                           0.009
% 43.50/6.00  unif_index_cands_time:                  0.
% 43.50/6.00  unif_index_add_time:                    0.
% 43.50/6.00  orderings_time:                         0.
% 43.50/6.00  out_proof_time:                         0.013
% 43.50/6.00  total_time:                             5.246
% 43.50/6.00  num_of_symbols:                         38
% 43.50/6.00  num_of_terms:                           300099
% 43.50/6.00  
% 43.50/6.00  ------ Preprocessing
% 43.50/6.00  
% 43.50/6.00  num_of_splits:                          0
% 43.50/6.00  num_of_split_atoms:                     0
% 43.50/6.00  num_of_reused_defs:                     0
% 43.50/6.00  num_eq_ax_congr_red:                    0
% 43.50/6.00  num_of_sem_filtered_clauses:            1
% 43.50/6.00  num_of_subtypes:                        0
% 43.50/6.00  monotx_restored_types:                  0
% 43.50/6.00  sat_num_of_epr_types:                   0
% 43.50/6.00  sat_num_of_non_cyclic_types:            0
% 43.50/6.00  sat_guarded_non_collapsed_types:        0
% 43.50/6.00  num_pure_diseq_elim:                    0
% 43.50/6.00  simp_replaced_by:                       0
% 43.50/6.00  res_preprocessed:                       50
% 43.50/6.00  prep_upred:                             0
% 43.50/6.00  prep_unflattend:                        0
% 43.50/6.00  smt_new_axioms:                         0
% 43.50/6.00  pred_elim_cands:                        1
% 43.50/6.00  pred_elim:                              0
% 43.50/6.00  pred_elim_cl:                           0
% 43.50/6.00  pred_elim_cycles:                       1
% 43.50/6.00  merged_defs:                            6
% 43.50/6.00  merged_defs_ncl:                        0
% 43.50/6.00  bin_hyper_res:                          6
% 43.50/6.00  prep_cycles:                            3
% 43.50/6.00  pred_elim_time:                         0.
% 43.50/6.00  splitting_time:                         0.
% 43.50/6.00  sem_filter_time:                        0.
% 43.50/6.00  monotx_time:                            0.
% 43.50/6.00  subtype_inf_time:                       0.
% 43.50/6.00  
% 43.50/6.00  ------ Problem properties
% 43.50/6.00  
% 43.50/6.00  clauses:                                13
% 43.50/6.00  conjectures:                            2
% 43.50/6.00  epr:                                    1
% 43.50/6.00  horn:                                   13
% 43.50/6.00  ground:                                 2
% 43.50/6.00  unary:                                  8
% 43.50/6.00  binary:                                 4
% 43.50/6.00  lits:                                   19
% 43.50/6.00  lits_eq:                                8
% 43.50/6.00  fd_pure:                                0
% 43.50/6.00  fd_pseudo:                              0
% 43.50/6.00  fd_cond:                                0
% 43.50/6.00  fd_pseudo_cond:                         0
% 43.50/6.00  ac_symbols:                             0
% 43.50/6.00  
% 43.50/6.00  ------ Propositional Solver
% 43.50/6.00  
% 43.50/6.00  prop_solver_calls:                      29
% 43.50/6.00  prop_fast_solver_calls:                 669
% 43.50/6.00  smt_solver_calls:                       0
% 43.50/6.00  smt_fast_solver_calls:                  0
% 43.50/6.00  prop_num_of_clauses:                    28387
% 43.50/6.00  prop_preprocess_simplified:             21669
% 43.50/6.00  prop_fo_subsumed:                       5
% 43.50/6.00  prop_solver_time:                       0.
% 43.50/6.00  smt_solver_time:                        0.
% 43.50/6.00  smt_fast_solver_time:                   0.
% 43.50/6.00  prop_fast_solver_time:                  0.
% 43.50/6.00  prop_unsat_core_time:                   0.
% 43.50/6.00  
% 43.50/6.00  ------ QBF
% 43.50/6.00  
% 43.50/6.00  qbf_q_res:                              0
% 43.50/6.00  qbf_num_tautologies:                    0
% 43.50/6.00  qbf_prep_cycles:                        0
% 43.50/6.00  
% 43.50/6.00  ------ BMC1
% 43.50/6.00  
% 43.50/6.00  bmc1_current_bound:                     -1
% 43.50/6.00  bmc1_last_solved_bound:                 -1
% 43.50/6.00  bmc1_unsat_core_size:                   -1
% 43.50/6.00  bmc1_unsat_core_parents_size:           -1
% 43.50/6.00  bmc1_merge_next_fun:                    0
% 43.50/6.00  bmc1_unsat_core_clauses_time:           0.
% 43.50/6.00  
% 43.50/6.00  ------ Instantiation
% 43.50/6.00  
% 43.50/6.00  inst_num_of_clauses:                    4142
% 43.50/6.00  inst_num_in_passive:                    810
% 43.50/6.00  inst_num_in_active:                     1512
% 43.50/6.00  inst_num_in_unprocessed:                1820
% 43.50/6.00  inst_num_of_loops:                      1620
% 43.50/6.00  inst_num_of_learning_restarts:          0
% 43.50/6.00  inst_num_moves_active_passive:          105
% 43.50/6.00  inst_lit_activity:                      0
% 43.50/6.00  inst_lit_activity_moves:                0
% 43.50/6.00  inst_num_tautologies:                   0
% 43.50/6.00  inst_num_prop_implied:                  0
% 43.50/6.00  inst_num_existing_simplified:           0
% 43.50/6.00  inst_num_eq_res_simplified:             0
% 43.50/6.00  inst_num_child_elim:                    0
% 43.50/6.00  inst_num_of_dismatching_blockings:      1949
% 43.50/6.00  inst_num_of_non_proper_insts:           5092
% 43.50/6.00  inst_num_of_duplicates:                 0
% 43.50/6.00  inst_inst_num_from_inst_to_res:         0
% 43.50/6.00  inst_dismatching_checking_time:         0.
% 43.50/6.00  
% 43.50/6.00  ------ Resolution
% 43.50/6.00  
% 43.50/6.00  res_num_of_clauses:                     0
% 43.50/6.00  res_num_in_passive:                     0
% 43.50/6.00  res_num_in_active:                      0
% 43.50/6.00  res_num_of_loops:                       53
% 43.50/6.00  res_forward_subset_subsumed:            473
% 43.50/6.00  res_backward_subset_subsumed:           4
% 43.50/6.00  res_forward_subsumed:                   0
% 43.50/6.00  res_backward_subsumed:                  0
% 43.50/6.00  res_forward_subsumption_resolution:     0
% 43.50/6.00  res_backward_subsumption_resolution:    0
% 43.50/6.00  res_clause_to_clause_subsumption:       126806
% 43.50/6.00  res_orphan_elimination:                 0
% 43.50/6.00  res_tautology_del:                      349
% 43.50/6.00  res_num_eq_res_simplified:              0
% 43.50/6.00  res_num_sel_changes:                    0
% 43.50/6.00  res_moves_from_active_to_pass:          0
% 43.50/6.00  
% 43.50/6.00  ------ Superposition
% 43.50/6.00  
% 43.50/6.00  sup_time_total:                         0.
% 43.50/6.00  sup_time_generating:                    0.
% 43.50/6.00  sup_time_sim_full:                      0.
% 43.50/6.00  sup_time_sim_immed:                     0.
% 43.50/6.00  
% 43.50/6.00  sup_num_of_clauses:                     6460
% 43.50/6.00  sup_num_in_active:                      241
% 43.50/6.00  sup_num_in_passive:                     6219
% 43.50/6.00  sup_num_of_loops:                       322
% 43.50/6.00  sup_fw_superposition:                   28044
% 43.50/6.00  sup_bw_superposition:                   27334
% 43.50/6.00  sup_immediate_simplified:               37482
% 43.50/6.00  sup_given_eliminated:                   37
% 43.50/6.00  comparisons_done:                       0
% 43.50/6.00  comparisons_avoided:                    0
% 43.50/6.00  
% 43.50/6.00  ------ Simplifications
% 43.50/6.00  
% 43.50/6.00  
% 43.50/6.00  sim_fw_subset_subsumed:                 117
% 43.50/6.00  sim_bw_subset_subsumed:                 1
% 43.50/6.00  sim_fw_subsumed:                        4291
% 43.50/6.00  sim_bw_subsumed:                        348
% 43.50/6.00  sim_fw_subsumption_res:                 0
% 43.50/6.00  sim_bw_subsumption_res:                 0
% 43.50/6.00  sim_tautology_del:                      472
% 43.50/6.00  sim_eq_tautology_del:                   14080
% 43.50/6.00  sim_eq_res_simp:                        1893
% 43.50/6.00  sim_fw_demodulated:                     47563
% 43.50/6.00  sim_bw_demodulated:                     534
% 43.50/6.00  sim_light_normalised:                   14174
% 43.50/6.00  sim_joinable_taut:                      0
% 43.50/6.00  sim_joinable_simp:                      0
% 43.50/6.00  sim_ac_normalised:                      0
% 43.50/6.00  sim_smt_subsumption:                    0
% 43.50/6.00  
%------------------------------------------------------------------------------
