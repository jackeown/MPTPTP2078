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
% DateTime   : Thu Dec  3 11:23:51 EST 2020

% Result     : Timeout 59.80s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  282 (47726 expanded)
%              Number of clauses        :  244 (19561 expanded)
%              Number of leaves         :   15 (12184 expanded)
%              Depth                    :   42
%              Number of atoms          :  333 (63811 expanded)
%              Number of equality atoms :  300 (53132 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_100,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_276,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_212937,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_458,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_14])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_616,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_3181,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_458,c_616])).

cnf(c_3613,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_3181])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_680,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_685,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_680,c_7])).

cnf(c_3645,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3613,c_685])).

cnf(c_530,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_1172,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_530])).

cnf(c_3171,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1172,c_616])).

cnf(c_3214,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3171,c_685])).

cnf(c_3215,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_3214,c_8])).

cnf(c_15919,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3215])).

cnf(c_37814,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_15919])).

cnf(c_186078,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK1),sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_3645,c_37814])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_263,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_264,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_526,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_263,c_264])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_265,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1013,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_526,c_265])).

cnf(c_1346,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_1013,c_10])).

cnf(c_603,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_2410,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_603,c_685])).

cnf(c_2413,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2410])).

cnf(c_3436,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1346,c_2413])).

cnf(c_1772,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1172,c_6])).

cnf(c_1774,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1772,c_685])).

cnf(c_3464,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_3436,c_685,c_1774])).

cnf(c_532,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_458,c_9])).

cnf(c_750,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_532,c_8])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_267,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_7])).

cnf(c_613,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_267,c_8])).

cnf(c_621,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_613,c_9])).

cnf(c_753,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_750,c_621])).

cnf(c_834,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_753,c_6])).

cnf(c_835,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_834,c_685])).

cnf(c_15969,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_3215])).

cnf(c_38742,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_15969,c_3181])).

cnf(c_614,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_620,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_614,c_8])).

cnf(c_5439,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK0),X1)) ),
    inference(superposition,[status(thm)],[c_458,c_620])).

cnf(c_5527,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) ),
    inference(demodulation,[status(thm)],[c_5439,c_620])).

cnf(c_39009,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),sK3),sK2)))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_38742,c_5527])).

cnf(c_39010,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),sK3),sK2)))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_39009,c_458])).

cnf(c_1769,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1172,c_8])).

cnf(c_1775,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1769,c_8,c_621])).

cnf(c_2636,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1775])).

cnf(c_4676,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2636,c_8])).

cnf(c_39536,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39010,c_4676])).

cnf(c_3177,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_616])).

cnf(c_62402,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2),sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_39536,c_3177])).

cnf(c_833,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_753,c_8])).

cnf(c_836,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_833,c_620,c_621])).

cnf(c_1004,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_836,c_6])).

cnf(c_1005,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1004,c_685])).

cnf(c_16060,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3215,c_5527])).

cnf(c_16066,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_16060,c_458])).

cnf(c_16833,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))),X0),k2_xboole_0(sK1,sK0))) = X0 ),
    inference(superposition,[status(thm)],[c_16066,c_3215])).

cnf(c_32502,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X1,X0))),sK3),sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_16833,c_3181])).

cnf(c_32889,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_458,c_32502])).

cnf(c_33166,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),sK3) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2)) ),
    inference(superposition,[status(thm)],[c_32889,c_2413])).

cnf(c_33226,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_33166,c_32889])).

cnf(c_40418,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1))),sK3),sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1005,c_33226])).

cnf(c_612,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_622,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_612,c_620,c_621])).

cnf(c_1173,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_458,c_530])).

cnf(c_3172,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1173,c_616])).

cnf(c_1011,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_263,c_265])).

cnf(c_1272,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_6])).

cnf(c_1273,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k4_xboole_0(sK3,sK1) ),
    inference(demodulation,[status(thm)],[c_1272,c_685])).

cnf(c_2037,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1273,c_0])).

cnf(c_2038,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_2037,c_1774])).

cnf(c_3212,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3172,c_2038])).

cnf(c_3213,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_3212,c_685])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_262,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_527,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_262,c_264])).

cnf(c_1014,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_527,c_265])).

cnf(c_1395,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_1014,c_10])).

cnf(c_3437,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1395,c_2413])).

cnf(c_3463,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3437,c_685,c_1774])).

cnf(c_40495,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_40418,c_622,c_685,c_3213,c_3463])).

cnf(c_62871,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK2),sK3)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_62402,c_40495])).

cnf(c_62872,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),k2_xboole_0(sK2,sK3))) = sK1 ),
    inference(demodulation,[status(thm)],[c_62871,c_8,c_685])).

cnf(c_62873,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),k2_xboole_0(sK1,sK0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_62872,c_458])).

cnf(c_62874,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK3)) = sK1 ),
    inference(demodulation,[status(thm)],[c_62873,c_3177,c_40495])).

cnf(c_1171,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_530])).

cnf(c_2491,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1171,c_8])).

cnf(c_2497,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2491,c_8,c_621])).

cnf(c_14510,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2497,c_8])).

cnf(c_34181,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k2_xboole_0(X1,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3215,c_14510])).

cnf(c_2431,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2410,c_0])).

cnf(c_34286,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34181,c_8,c_2431])).

cnf(c_179749,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(X1,X0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_62874,c_34286])).

cnf(c_180468,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_835,c_179749])).

cnf(c_4897,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3645,c_2636])).

cnf(c_4900,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4897,c_8])).

cnf(c_7480,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4900])).

cnf(c_9363,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_7480])).

cnf(c_11620,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),sK1) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9363,c_6])).

cnf(c_11629,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),sK1) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_11620,c_685])).

cnf(c_2493,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1171,c_6])).

cnf(c_2496,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2493,c_685])).

cnf(c_3619,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1172,c_3181])).

cnf(c_3638,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_3619,c_8,c_685])).

cnf(c_16339,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3638,c_5527])).

cnf(c_16340,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_16339,c_458])).

cnf(c_17003,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))),X0),k2_xboole_0(sK1,sK0))) = X0 ),
    inference(superposition,[status(thm)],[c_16340,c_3215])).

cnf(c_44205,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X1,sK2))),X0),k2_xboole_0(sK1,sK3))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_17003,c_17003,c_40495])).

cnf(c_91954,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k2_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_2496,c_44205])).

cnf(c_678,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_10])).

cnf(c_687,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_678,c_267])).

cnf(c_44287,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k1_xboole_0),k2_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44205,c_687])).

cnf(c_44384,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k2_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44287,c_685])).

cnf(c_91966,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) ),
    inference(light_normalisation,[status(thm)],[c_91954,c_44384])).

cnf(c_91967,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_91966,c_8,c_620,c_685])).

cnf(c_91968,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_91967,c_458])).

cnf(c_91969,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91968,c_530,c_620,c_40495])).

cnf(c_3179,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_616])).

cnf(c_117906,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK2),sK3))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)))) ),
    inference(superposition,[status(thm)],[c_91969,c_3179])).

cnf(c_94256,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_91969,c_6])).

cnf(c_91570,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2410,c_2496])).

cnf(c_1180,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_530,c_6])).

cnf(c_1182,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1180,c_685])).

cnf(c_41004,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_2413,c_1182])).

cnf(c_41220,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_41004,c_1182])).

cnf(c_92363,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_91570,c_9,c_41220])).

cnf(c_94307,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_94256,c_92363])).

cnf(c_118797,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,sK2),sK3))) ),
    inference(light_normalisation,[status(thm)],[c_117906,c_91969,c_94307])).

cnf(c_92552,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_92363,c_616])).

cnf(c_679,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_686,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_679,c_8])).

cnf(c_10509,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_686,c_3177])).

cnf(c_10654,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,X1))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_2410,c_10509])).

cnf(c_3482,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_10,c_2431])).

cnf(c_3517,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3482,c_10])).

cnf(c_5910,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_3517])).

cnf(c_3446,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2413,c_0])).

cnf(c_5845,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_10,c_3446])).

cnf(c_683,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_5892,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5845,c_683])).

cnf(c_5977,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5910,c_8,c_5892])).

cnf(c_5978,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5977,c_3177])).

cnf(c_10747,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_10654,c_620,c_5978])).

cnf(c_1181,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_530,c_8])).

cnf(c_10748,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_10747,c_1181])).

cnf(c_92637,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_92552,c_10748])).

cnf(c_118798,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_118797,c_620,c_92637])).

cnf(c_118799,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_118798,c_458])).

cnf(c_118800,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK3))) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(demodulation,[status(thm)],[c_118799,c_40495])).

cnf(c_3442,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2413,c_9])).

cnf(c_122038,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),X0),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_118800,c_3442])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_167166,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK3),X0)) != k1_xboole_0
    | k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_122038,c_5])).

cnf(c_15994,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK0)),X0),k2_xboole_0(sK3,k4_xboole_0(X1,sK2)))) = X0 ),
    inference(superposition,[status(thm)],[c_3181,c_3215])).

cnf(c_71257,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,k4_xboole_0(X0,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) ),
    inference(superposition,[status(thm)],[c_1774,c_15994])).

cnf(c_3628,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3181,c_530])).

cnf(c_71284,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK3)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK3)),X1) ),
    inference(light_normalisation,[status(thm)],[c_71257,c_3628,c_40495])).

cnf(c_71285,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK3),X1)) ),
    inference(demodulation,[status(thm)],[c_71284,c_8,c_620,c_685])).

cnf(c_33188,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),k2_xboole_0(X1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32889,c_4676])).

cnf(c_45673,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),sK3),sK2),k2_xboole_0(X1,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33188,c_33188,c_40495])).

cnf(c_45674,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k2_xboole_0(sK2,k2_xboole_0(X1,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45673,c_8,c_41220])).

cnf(c_117881,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k2_xboole_0(sK2,k2_xboole_0(X1,sK3))),k4_xboole_0(X2,k2_xboole_0(sK2,k2_xboole_0(X1,sK3)))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(X1,sK3)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3)))) ),
    inference(superposition,[status(thm)],[c_45674,c_3179])).

cnf(c_41042,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1182,c_0])).

cnf(c_3614,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_267,c_3181])).

cnf(c_3644,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3614,c_685])).

cnf(c_2660,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1775,c_6])).

cnf(c_2662,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2660,c_685])).

cnf(c_101517,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2662])).

cnf(c_102802,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_101517,c_0])).

cnf(c_104243,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),X0),sK3) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) ),
    inference(superposition,[status(thm)],[c_3644,c_102802])).

cnf(c_5155,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_3644,c_2413])).

cnf(c_5166,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_5155,c_3644])).

cnf(c_104558,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),sK2),X0),sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_104243,c_5166,c_40495])).

cnf(c_104559,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,X0)),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_104558,c_8])).

cnf(c_104724,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_41042,c_104559])).

cnf(c_118854,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(X1,sK3)),sK3))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X1,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_117881,c_45674,c_104724])).

cnf(c_16832,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X1,X0)),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16066,c_4676])).

cnf(c_17299,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16832,c_8])).

cnf(c_109932,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17299,c_17299,c_40495])).

cnf(c_5952,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3517,c_616])).

cnf(c_5958,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_5952,c_6])).

cnf(c_110102,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,sK3),k1_xboole_0))) = k2_xboole_0(k2_xboole_0(X0,sK3),X1) ),
    inference(superposition,[status(thm)],[c_109932,c_5958])).

cnf(c_3501,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_2431,c_616])).

cnf(c_3509,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3501,c_6])).

cnf(c_68905,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),X2) ),
    inference(superposition,[status(thm)],[c_1182,c_3509])).

cnf(c_69658,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_68905,c_2413])).

cnf(c_68899,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = k2_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_683,c_3509])).

cnf(c_69673,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_68899,c_683])).

cnf(c_110161,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),X1) = k2_xboole_0(k2_xboole_0(sK3,X0),X1) ),
    inference(demodulation,[status(thm)],[c_110102,c_7,c_69658,c_69673])).

cnf(c_110992,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,sK3),X2)) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_110161,c_620])).

cnf(c_110662,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,sK3)) = k2_xboole_0(k2_xboole_0(sK3,X1),X0) ),
    inference(superposition,[status(thm)],[c_110161,c_0])).

cnf(c_113690,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,X1),k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,sK3)),X3)) ),
    inference(superposition,[status(thm)],[c_110662,c_620])).

cnf(c_110723,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,X2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,X1),X2)) ),
    inference(superposition,[status(thm)],[c_110161,c_620])).

cnf(c_114015,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,sK3)),X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(sK3,k2_xboole_0(X1,X3)))) ),
    inference(demodulation,[status(thm)],[c_113690,c_620,c_110723])).

cnf(c_118855,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)),X1)) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(demodulation,[status(thm)],[c_118854,c_92637,c_110992,c_114015])).

cnf(c_1339,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1173,c_6])).

cnf(c_1340,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_1339,c_685])).

cnf(c_2311,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_1340,c_0])).

cnf(c_118856,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_118855,c_458,c_2311])).

cnf(c_118857,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(demodulation,[status(thm)],[c_118856,c_620,c_40495])).

cnf(c_123256,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_118857,c_267])).

cnf(c_167223,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_167166,c_71285,c_123256])).

cnf(c_167224,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_167223])).

cnf(c_180784,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_180468,c_11629,c_40495,c_167224])).

cnf(c_176629,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK3,X0)),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) != k1_xboole_0
    | k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_123256,c_5])).

cnf(c_176689,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_176629,c_267,c_118857])).

cnf(c_176690,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_176689])).

cnf(c_180785,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_180784,c_118857,c_176690])).

cnf(c_180970,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0),k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_180785,c_10])).

cnf(c_41358,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_41042])).

cnf(c_41598,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_6,c_41358])).

cnf(c_41842,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_41598,c_41358])).

cnf(c_181050,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_180970,c_7,c_41842,c_92363])).

cnf(c_62297,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_532,c_3177])).

cnf(c_1012,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_262,c_265])).

cnf(c_1281,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1012,c_6])).

cnf(c_1282,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k4_xboole_0(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_1281,c_685])).

cnf(c_2046,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1282,c_0])).

cnf(c_2047,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2046,c_1774])).

cnf(c_63025,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_62297,c_2047])).

cnf(c_63026,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_63025,c_685])).

cnf(c_181051,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_181050,c_63026])).

cnf(c_187365,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_186078,c_3464,c_181051])).

cnf(c_99,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2383,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_552,plain,
    ( k4_xboole_0(sK1,X0) != k4_xboole_0(X0,sK1)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1117,plain,
    ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_212937,c_187365,c_2383,c_1117,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:05:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 59.80/8.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.80/8.02  
% 59.80/8.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.80/8.02  
% 59.80/8.02  ------  iProver source info
% 59.80/8.02  
% 59.80/8.02  git: date: 2020-06-30 10:37:57 +0100
% 59.80/8.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.80/8.02  git: non_committed_changes: false
% 59.80/8.02  git: last_make_outside_of_git: false
% 59.80/8.02  
% 59.80/8.02  ------ 
% 59.80/8.02  
% 59.80/8.02  ------ Input Options
% 59.80/8.02  
% 59.80/8.02  --out_options                           all
% 59.80/8.02  --tptp_safe_out                         true
% 59.80/8.02  --problem_path                          ""
% 59.80/8.02  --include_path                          ""
% 59.80/8.02  --clausifier                            res/vclausify_rel
% 59.80/8.02  --clausifier_options                    ""
% 59.80/8.02  --stdin                                 false
% 59.80/8.02  --stats_out                             all
% 59.80/8.02  
% 59.80/8.02  ------ General Options
% 59.80/8.02  
% 59.80/8.02  --fof                                   false
% 59.80/8.02  --time_out_real                         305.
% 59.80/8.02  --time_out_virtual                      -1.
% 59.80/8.02  --symbol_type_check                     false
% 59.80/8.02  --clausify_out                          false
% 59.80/8.02  --sig_cnt_out                           false
% 59.80/8.02  --trig_cnt_out                          false
% 59.80/8.02  --trig_cnt_out_tolerance                1.
% 59.80/8.02  --trig_cnt_out_sk_spl                   false
% 59.80/8.02  --abstr_cl_out                          false
% 59.80/8.02  
% 59.80/8.02  ------ Global Options
% 59.80/8.02  
% 59.80/8.02  --schedule                              default
% 59.80/8.02  --add_important_lit                     false
% 59.80/8.02  --prop_solver_per_cl                    1000
% 59.80/8.02  --min_unsat_core                        false
% 59.80/8.02  --soft_assumptions                      false
% 59.80/8.02  --soft_lemma_size                       3
% 59.80/8.02  --prop_impl_unit_size                   0
% 59.80/8.02  --prop_impl_unit                        []
% 59.80/8.02  --share_sel_clauses                     true
% 59.80/8.02  --reset_solvers                         false
% 59.80/8.02  --bc_imp_inh                            [conj_cone]
% 59.80/8.02  --conj_cone_tolerance                   3.
% 59.80/8.02  --extra_neg_conj                        none
% 59.80/8.02  --large_theory_mode                     true
% 59.80/8.02  --prolific_symb_bound                   200
% 59.80/8.02  --lt_threshold                          2000
% 59.80/8.02  --clause_weak_htbl                      true
% 59.80/8.02  --gc_record_bc_elim                     false
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing Options
% 59.80/8.02  
% 59.80/8.02  --preprocessing_flag                    true
% 59.80/8.02  --time_out_prep_mult                    0.1
% 59.80/8.02  --splitting_mode                        input
% 59.80/8.02  --splitting_grd                         true
% 59.80/8.02  --splitting_cvd                         false
% 59.80/8.02  --splitting_cvd_svl                     false
% 59.80/8.02  --splitting_nvd                         32
% 59.80/8.02  --sub_typing                            true
% 59.80/8.02  --prep_gs_sim                           true
% 59.80/8.02  --prep_unflatten                        true
% 59.80/8.02  --prep_res_sim                          true
% 59.80/8.02  --prep_upred                            true
% 59.80/8.02  --prep_sem_filter                       exhaustive
% 59.80/8.02  --prep_sem_filter_out                   false
% 59.80/8.02  --pred_elim                             true
% 59.80/8.02  --res_sim_input                         true
% 59.80/8.02  --eq_ax_congr_red                       true
% 59.80/8.02  --pure_diseq_elim                       true
% 59.80/8.02  --brand_transform                       false
% 59.80/8.02  --non_eq_to_eq                          false
% 59.80/8.02  --prep_def_merge                        true
% 59.80/8.02  --prep_def_merge_prop_impl              false
% 59.80/8.02  --prep_def_merge_mbd                    true
% 59.80/8.02  --prep_def_merge_tr_red                 false
% 59.80/8.02  --prep_def_merge_tr_cl                  false
% 59.80/8.02  --smt_preprocessing                     true
% 59.80/8.02  --smt_ac_axioms                         fast
% 59.80/8.02  --preprocessed_out                      false
% 59.80/8.02  --preprocessed_stats                    false
% 59.80/8.02  
% 59.80/8.02  ------ Abstraction refinement Options
% 59.80/8.02  
% 59.80/8.02  --abstr_ref                             []
% 59.80/8.02  --abstr_ref_prep                        false
% 59.80/8.02  --abstr_ref_until_sat                   false
% 59.80/8.02  --abstr_ref_sig_restrict                funpre
% 59.80/8.02  --abstr_ref_af_restrict_to_split_sk     false
% 59.80/8.02  --abstr_ref_under                       []
% 59.80/8.02  
% 59.80/8.02  ------ SAT Options
% 59.80/8.02  
% 59.80/8.02  --sat_mode                              false
% 59.80/8.02  --sat_fm_restart_options                ""
% 59.80/8.02  --sat_gr_def                            false
% 59.80/8.02  --sat_epr_types                         true
% 59.80/8.02  --sat_non_cyclic_types                  false
% 59.80/8.02  --sat_finite_models                     false
% 59.80/8.02  --sat_fm_lemmas                         false
% 59.80/8.02  --sat_fm_prep                           false
% 59.80/8.02  --sat_fm_uc_incr                        true
% 59.80/8.02  --sat_out_model                         small
% 59.80/8.02  --sat_out_clauses                       false
% 59.80/8.02  
% 59.80/8.02  ------ QBF Options
% 59.80/8.02  
% 59.80/8.02  --qbf_mode                              false
% 59.80/8.02  --qbf_elim_univ                         false
% 59.80/8.02  --qbf_dom_inst                          none
% 59.80/8.02  --qbf_dom_pre_inst                      false
% 59.80/8.02  --qbf_sk_in                             false
% 59.80/8.02  --qbf_pred_elim                         true
% 59.80/8.02  --qbf_split                             512
% 59.80/8.02  
% 59.80/8.02  ------ BMC1 Options
% 59.80/8.02  
% 59.80/8.02  --bmc1_incremental                      false
% 59.80/8.02  --bmc1_axioms                           reachable_all
% 59.80/8.02  --bmc1_min_bound                        0
% 59.80/8.02  --bmc1_max_bound                        -1
% 59.80/8.02  --bmc1_max_bound_default                -1
% 59.80/8.02  --bmc1_symbol_reachability              true
% 59.80/8.02  --bmc1_property_lemmas                  false
% 59.80/8.02  --bmc1_k_induction                      false
% 59.80/8.02  --bmc1_non_equiv_states                 false
% 59.80/8.02  --bmc1_deadlock                         false
% 59.80/8.02  --bmc1_ucm                              false
% 59.80/8.02  --bmc1_add_unsat_core                   none
% 59.80/8.02  --bmc1_unsat_core_children              false
% 59.80/8.02  --bmc1_unsat_core_extrapolate_axioms    false
% 59.80/8.02  --bmc1_out_stat                         full
% 59.80/8.02  --bmc1_ground_init                      false
% 59.80/8.02  --bmc1_pre_inst_next_state              false
% 59.80/8.02  --bmc1_pre_inst_state                   false
% 59.80/8.02  --bmc1_pre_inst_reach_state             false
% 59.80/8.02  --bmc1_out_unsat_core                   false
% 59.80/8.02  --bmc1_aig_witness_out                  false
% 59.80/8.02  --bmc1_verbose                          false
% 59.80/8.02  --bmc1_dump_clauses_tptp                false
% 59.80/8.02  --bmc1_dump_unsat_core_tptp             false
% 59.80/8.02  --bmc1_dump_file                        -
% 59.80/8.02  --bmc1_ucm_expand_uc_limit              128
% 59.80/8.02  --bmc1_ucm_n_expand_iterations          6
% 59.80/8.02  --bmc1_ucm_extend_mode                  1
% 59.80/8.02  --bmc1_ucm_init_mode                    2
% 59.80/8.02  --bmc1_ucm_cone_mode                    none
% 59.80/8.02  --bmc1_ucm_reduced_relation_type        0
% 59.80/8.02  --bmc1_ucm_relax_model                  4
% 59.80/8.02  --bmc1_ucm_full_tr_after_sat            true
% 59.80/8.02  --bmc1_ucm_expand_neg_assumptions       false
% 59.80/8.02  --bmc1_ucm_layered_model                none
% 59.80/8.02  --bmc1_ucm_max_lemma_size               10
% 59.80/8.02  
% 59.80/8.02  ------ AIG Options
% 59.80/8.02  
% 59.80/8.02  --aig_mode                              false
% 59.80/8.02  
% 59.80/8.02  ------ Instantiation Options
% 59.80/8.02  
% 59.80/8.02  --instantiation_flag                    true
% 59.80/8.02  --inst_sos_flag                         true
% 59.80/8.02  --inst_sos_phase                        true
% 59.80/8.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.80/8.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.80/8.02  --inst_lit_sel_side                     num_symb
% 59.80/8.02  --inst_solver_per_active                1400
% 59.80/8.02  --inst_solver_calls_frac                1.
% 59.80/8.02  --inst_passive_queue_type               priority_queues
% 59.80/8.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.80/8.02  --inst_passive_queues_freq              [25;2]
% 59.80/8.02  --inst_dismatching                      true
% 59.80/8.02  --inst_eager_unprocessed_to_passive     true
% 59.80/8.02  --inst_prop_sim_given                   true
% 59.80/8.02  --inst_prop_sim_new                     false
% 59.80/8.02  --inst_subs_new                         false
% 59.80/8.02  --inst_eq_res_simp                      false
% 59.80/8.02  --inst_subs_given                       false
% 59.80/8.02  --inst_orphan_elimination               true
% 59.80/8.02  --inst_learning_loop_flag               true
% 59.80/8.02  --inst_learning_start                   3000
% 59.80/8.02  --inst_learning_factor                  2
% 59.80/8.02  --inst_start_prop_sim_after_learn       3
% 59.80/8.02  --inst_sel_renew                        solver
% 59.80/8.02  --inst_lit_activity_flag                true
% 59.80/8.02  --inst_restr_to_given                   false
% 59.80/8.02  --inst_activity_threshold               500
% 59.80/8.02  --inst_out_proof                        true
% 59.80/8.02  
% 59.80/8.02  ------ Resolution Options
% 59.80/8.02  
% 59.80/8.02  --resolution_flag                       true
% 59.80/8.02  --res_lit_sel                           adaptive
% 59.80/8.02  --res_lit_sel_side                      none
% 59.80/8.02  --res_ordering                          kbo
% 59.80/8.02  --res_to_prop_solver                    active
% 59.80/8.02  --res_prop_simpl_new                    false
% 59.80/8.02  --res_prop_simpl_given                  true
% 59.80/8.02  --res_passive_queue_type                priority_queues
% 59.80/8.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.80/8.02  --res_passive_queues_freq               [15;5]
% 59.80/8.02  --res_forward_subs                      full
% 59.80/8.02  --res_backward_subs                     full
% 59.80/8.02  --res_forward_subs_resolution           true
% 59.80/8.02  --res_backward_subs_resolution          true
% 59.80/8.02  --res_orphan_elimination                true
% 59.80/8.02  --res_time_limit                        2.
% 59.80/8.02  --res_out_proof                         true
% 59.80/8.02  
% 59.80/8.02  ------ Superposition Options
% 59.80/8.02  
% 59.80/8.02  --superposition_flag                    true
% 59.80/8.02  --sup_passive_queue_type                priority_queues
% 59.80/8.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.80/8.02  --sup_passive_queues_freq               [8;1;4]
% 59.80/8.02  --demod_completeness_check              fast
% 59.80/8.02  --demod_use_ground                      true
% 59.80/8.02  --sup_to_prop_solver                    passive
% 59.80/8.02  --sup_prop_simpl_new                    true
% 59.80/8.02  --sup_prop_simpl_given                  true
% 59.80/8.02  --sup_fun_splitting                     true
% 59.80/8.02  --sup_smt_interval                      50000
% 59.80/8.02  
% 59.80/8.02  ------ Superposition Simplification Setup
% 59.80/8.02  
% 59.80/8.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.80/8.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.80/8.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.80/8.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.80/8.02  --sup_full_triv                         [TrivRules;PropSubs]
% 59.80/8.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.80/8.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.80/8.02  --sup_immed_triv                        [TrivRules]
% 59.80/8.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_immed_bw_main                     []
% 59.80/8.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.80/8.02  --sup_input_triv                        [Unflattening;TrivRules]
% 59.80/8.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_input_bw                          []
% 59.80/8.02  
% 59.80/8.02  ------ Combination Options
% 59.80/8.02  
% 59.80/8.02  --comb_res_mult                         3
% 59.80/8.02  --comb_sup_mult                         2
% 59.80/8.02  --comb_inst_mult                        10
% 59.80/8.02  
% 59.80/8.02  ------ Debug Options
% 59.80/8.02  
% 59.80/8.02  --dbg_backtrace                         false
% 59.80/8.02  --dbg_dump_prop_clauses                 false
% 59.80/8.02  --dbg_dump_prop_clauses_file            -
% 59.80/8.02  --dbg_out_stat                          false
% 59.80/8.02  ------ Parsing...
% 59.80/8.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.80/8.02  ------ Proving...
% 59.80/8.02  ------ Problem Properties 
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  clauses                                 15
% 59.80/8.02  conjectures                             4
% 59.80/8.02  EPR                                     4
% 59.80/8.02  Horn                                    15
% 59.80/8.02  unary                                   11
% 59.80/8.02  binary                                  4
% 59.80/8.02  lits                                    19
% 59.80/8.02  lits eq                                 13
% 59.80/8.02  fd_pure                                 0
% 59.80/8.02  fd_pseudo                               0
% 59.80/8.02  fd_cond                                 0
% 59.80/8.02  fd_pseudo_cond                          1
% 59.80/8.02  AC symbols                              0
% 59.80/8.02  
% 59.80/8.02  ------ Schedule dynamic 5 is on 
% 59.80/8.02  
% 59.80/8.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  ------ 
% 59.80/8.02  Current options:
% 59.80/8.02  ------ 
% 59.80/8.02  
% 59.80/8.02  ------ Input Options
% 59.80/8.02  
% 59.80/8.02  --out_options                           all
% 59.80/8.02  --tptp_safe_out                         true
% 59.80/8.02  --problem_path                          ""
% 59.80/8.02  --include_path                          ""
% 59.80/8.02  --clausifier                            res/vclausify_rel
% 59.80/8.02  --clausifier_options                    ""
% 59.80/8.02  --stdin                                 false
% 59.80/8.02  --stats_out                             all
% 59.80/8.02  
% 59.80/8.02  ------ General Options
% 59.80/8.02  
% 59.80/8.02  --fof                                   false
% 59.80/8.02  --time_out_real                         305.
% 59.80/8.02  --time_out_virtual                      -1.
% 59.80/8.02  --symbol_type_check                     false
% 59.80/8.02  --clausify_out                          false
% 59.80/8.02  --sig_cnt_out                           false
% 59.80/8.02  --trig_cnt_out                          false
% 59.80/8.02  --trig_cnt_out_tolerance                1.
% 59.80/8.02  --trig_cnt_out_sk_spl                   false
% 59.80/8.02  --abstr_cl_out                          false
% 59.80/8.02  
% 59.80/8.02  ------ Global Options
% 59.80/8.02  
% 59.80/8.02  --schedule                              default
% 59.80/8.02  --add_important_lit                     false
% 59.80/8.02  --prop_solver_per_cl                    1000
% 59.80/8.02  --min_unsat_core                        false
% 59.80/8.02  --soft_assumptions                      false
% 59.80/8.02  --soft_lemma_size                       3
% 59.80/8.02  --prop_impl_unit_size                   0
% 59.80/8.02  --prop_impl_unit                        []
% 59.80/8.02  --share_sel_clauses                     true
% 59.80/8.02  --reset_solvers                         false
% 59.80/8.02  --bc_imp_inh                            [conj_cone]
% 59.80/8.02  --conj_cone_tolerance                   3.
% 59.80/8.02  --extra_neg_conj                        none
% 59.80/8.02  --large_theory_mode                     true
% 59.80/8.02  --prolific_symb_bound                   200
% 59.80/8.02  --lt_threshold                          2000
% 59.80/8.02  --clause_weak_htbl                      true
% 59.80/8.02  --gc_record_bc_elim                     false
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing Options
% 59.80/8.02  
% 59.80/8.02  --preprocessing_flag                    true
% 59.80/8.02  --time_out_prep_mult                    0.1
% 59.80/8.02  --splitting_mode                        input
% 59.80/8.02  --splitting_grd                         true
% 59.80/8.02  --splitting_cvd                         false
% 59.80/8.02  --splitting_cvd_svl                     false
% 59.80/8.02  --splitting_nvd                         32
% 59.80/8.02  --sub_typing                            true
% 59.80/8.02  --prep_gs_sim                           true
% 59.80/8.02  --prep_unflatten                        true
% 59.80/8.02  --prep_res_sim                          true
% 59.80/8.02  --prep_upred                            true
% 59.80/8.02  --prep_sem_filter                       exhaustive
% 59.80/8.02  --prep_sem_filter_out                   false
% 59.80/8.02  --pred_elim                             true
% 59.80/8.02  --res_sim_input                         true
% 59.80/8.02  --eq_ax_congr_red                       true
% 59.80/8.02  --pure_diseq_elim                       true
% 59.80/8.02  --brand_transform                       false
% 59.80/8.02  --non_eq_to_eq                          false
% 59.80/8.02  --prep_def_merge                        true
% 59.80/8.02  --prep_def_merge_prop_impl              false
% 59.80/8.02  --prep_def_merge_mbd                    true
% 59.80/8.02  --prep_def_merge_tr_red                 false
% 59.80/8.02  --prep_def_merge_tr_cl                  false
% 59.80/8.02  --smt_preprocessing                     true
% 59.80/8.02  --smt_ac_axioms                         fast
% 59.80/8.02  --preprocessed_out                      false
% 59.80/8.02  --preprocessed_stats                    false
% 59.80/8.02  
% 59.80/8.02  ------ Abstraction refinement Options
% 59.80/8.02  
% 59.80/8.02  --abstr_ref                             []
% 59.80/8.02  --abstr_ref_prep                        false
% 59.80/8.02  --abstr_ref_until_sat                   false
% 59.80/8.02  --abstr_ref_sig_restrict                funpre
% 59.80/8.02  --abstr_ref_af_restrict_to_split_sk     false
% 59.80/8.02  --abstr_ref_under                       []
% 59.80/8.02  
% 59.80/8.02  ------ SAT Options
% 59.80/8.02  
% 59.80/8.02  --sat_mode                              false
% 59.80/8.02  --sat_fm_restart_options                ""
% 59.80/8.02  --sat_gr_def                            false
% 59.80/8.02  --sat_epr_types                         true
% 59.80/8.02  --sat_non_cyclic_types                  false
% 59.80/8.02  --sat_finite_models                     false
% 59.80/8.02  --sat_fm_lemmas                         false
% 59.80/8.02  --sat_fm_prep                           false
% 59.80/8.02  --sat_fm_uc_incr                        true
% 59.80/8.02  --sat_out_model                         small
% 59.80/8.02  --sat_out_clauses                       false
% 59.80/8.02  
% 59.80/8.02  ------ QBF Options
% 59.80/8.02  
% 59.80/8.02  --qbf_mode                              false
% 59.80/8.02  --qbf_elim_univ                         false
% 59.80/8.02  --qbf_dom_inst                          none
% 59.80/8.02  --qbf_dom_pre_inst                      false
% 59.80/8.02  --qbf_sk_in                             false
% 59.80/8.02  --qbf_pred_elim                         true
% 59.80/8.02  --qbf_split                             512
% 59.80/8.02  
% 59.80/8.02  ------ BMC1 Options
% 59.80/8.02  
% 59.80/8.02  --bmc1_incremental                      false
% 59.80/8.02  --bmc1_axioms                           reachable_all
% 59.80/8.02  --bmc1_min_bound                        0
% 59.80/8.02  --bmc1_max_bound                        -1
% 59.80/8.02  --bmc1_max_bound_default                -1
% 59.80/8.02  --bmc1_symbol_reachability              true
% 59.80/8.02  --bmc1_property_lemmas                  false
% 59.80/8.02  --bmc1_k_induction                      false
% 59.80/8.02  --bmc1_non_equiv_states                 false
% 59.80/8.02  --bmc1_deadlock                         false
% 59.80/8.02  --bmc1_ucm                              false
% 59.80/8.02  --bmc1_add_unsat_core                   none
% 59.80/8.02  --bmc1_unsat_core_children              false
% 59.80/8.02  --bmc1_unsat_core_extrapolate_axioms    false
% 59.80/8.02  --bmc1_out_stat                         full
% 59.80/8.02  --bmc1_ground_init                      false
% 59.80/8.02  --bmc1_pre_inst_next_state              false
% 59.80/8.02  --bmc1_pre_inst_state                   false
% 59.80/8.02  --bmc1_pre_inst_reach_state             false
% 59.80/8.02  --bmc1_out_unsat_core                   false
% 59.80/8.02  --bmc1_aig_witness_out                  false
% 59.80/8.02  --bmc1_verbose                          false
% 59.80/8.02  --bmc1_dump_clauses_tptp                false
% 59.80/8.02  --bmc1_dump_unsat_core_tptp             false
% 59.80/8.02  --bmc1_dump_file                        -
% 59.80/8.02  --bmc1_ucm_expand_uc_limit              128
% 59.80/8.02  --bmc1_ucm_n_expand_iterations          6
% 59.80/8.02  --bmc1_ucm_extend_mode                  1
% 59.80/8.02  --bmc1_ucm_init_mode                    2
% 59.80/8.02  --bmc1_ucm_cone_mode                    none
% 59.80/8.02  --bmc1_ucm_reduced_relation_type        0
% 59.80/8.02  --bmc1_ucm_relax_model                  4
% 59.80/8.02  --bmc1_ucm_full_tr_after_sat            true
% 59.80/8.02  --bmc1_ucm_expand_neg_assumptions       false
% 59.80/8.02  --bmc1_ucm_layered_model                none
% 59.80/8.02  --bmc1_ucm_max_lemma_size               10
% 59.80/8.02  
% 59.80/8.02  ------ AIG Options
% 59.80/8.02  
% 59.80/8.02  --aig_mode                              false
% 59.80/8.02  
% 59.80/8.02  ------ Instantiation Options
% 59.80/8.02  
% 59.80/8.02  --instantiation_flag                    true
% 59.80/8.02  --inst_sos_flag                         true
% 59.80/8.02  --inst_sos_phase                        true
% 59.80/8.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.80/8.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.80/8.02  --inst_lit_sel_side                     none
% 59.80/8.02  --inst_solver_per_active                1400
% 59.80/8.02  --inst_solver_calls_frac                1.
% 59.80/8.02  --inst_passive_queue_type               priority_queues
% 59.80/8.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.80/8.02  --inst_passive_queues_freq              [25;2]
% 59.80/8.02  --inst_dismatching                      true
% 59.80/8.02  --inst_eager_unprocessed_to_passive     true
% 59.80/8.02  --inst_prop_sim_given                   true
% 59.80/8.02  --inst_prop_sim_new                     false
% 59.80/8.02  --inst_subs_new                         false
% 59.80/8.02  --inst_eq_res_simp                      false
% 59.80/8.02  --inst_subs_given                       false
% 59.80/8.02  --inst_orphan_elimination               true
% 59.80/8.02  --inst_learning_loop_flag               true
% 59.80/8.02  --inst_learning_start                   3000
% 59.80/8.02  --inst_learning_factor                  2
% 59.80/8.02  --inst_start_prop_sim_after_learn       3
% 59.80/8.02  --inst_sel_renew                        solver
% 59.80/8.02  --inst_lit_activity_flag                true
% 59.80/8.02  --inst_restr_to_given                   false
% 59.80/8.02  --inst_activity_threshold               500
% 59.80/8.02  --inst_out_proof                        true
% 59.80/8.02  
% 59.80/8.02  ------ Resolution Options
% 59.80/8.02  
% 59.80/8.02  --resolution_flag                       false
% 59.80/8.02  --res_lit_sel                           adaptive
% 59.80/8.02  --res_lit_sel_side                      none
% 59.80/8.02  --res_ordering                          kbo
% 59.80/8.02  --res_to_prop_solver                    active
% 59.80/8.02  --res_prop_simpl_new                    false
% 59.80/8.02  --res_prop_simpl_given                  true
% 59.80/8.02  --res_passive_queue_type                priority_queues
% 59.80/8.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.80/8.02  --res_passive_queues_freq               [15;5]
% 59.80/8.02  --res_forward_subs                      full
% 59.80/8.02  --res_backward_subs                     full
% 59.80/8.02  --res_forward_subs_resolution           true
% 59.80/8.02  --res_backward_subs_resolution          true
% 59.80/8.02  --res_orphan_elimination                true
% 59.80/8.02  --res_time_limit                        2.
% 59.80/8.02  --res_out_proof                         true
% 59.80/8.02  
% 59.80/8.02  ------ Superposition Options
% 59.80/8.02  
% 59.80/8.02  --superposition_flag                    true
% 59.80/8.02  --sup_passive_queue_type                priority_queues
% 59.80/8.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.80/8.02  --sup_passive_queues_freq               [8;1;4]
% 59.80/8.02  --demod_completeness_check              fast
% 59.80/8.02  --demod_use_ground                      true
% 59.80/8.02  --sup_to_prop_solver                    passive
% 59.80/8.02  --sup_prop_simpl_new                    true
% 59.80/8.02  --sup_prop_simpl_given                  true
% 59.80/8.02  --sup_fun_splitting                     true
% 59.80/8.02  --sup_smt_interval                      50000
% 59.80/8.02  
% 59.80/8.02  ------ Superposition Simplification Setup
% 59.80/8.02  
% 59.80/8.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.80/8.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.80/8.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.80/8.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.80/8.02  --sup_full_triv                         [TrivRules;PropSubs]
% 59.80/8.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.80/8.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.80/8.02  --sup_immed_triv                        [TrivRules]
% 59.80/8.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_immed_bw_main                     []
% 59.80/8.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.80/8.02  --sup_input_triv                        [Unflattening;TrivRules]
% 59.80/8.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.80/8.02  --sup_input_bw                          []
% 59.80/8.02  
% 59.80/8.02  ------ Combination Options
% 59.80/8.02  
% 59.80/8.02  --comb_res_mult                         3
% 59.80/8.02  --comb_sup_mult                         2
% 59.80/8.02  --comb_inst_mult                        10
% 59.80/8.02  
% 59.80/8.02  ------ Debug Options
% 59.80/8.02  
% 59.80/8.02  --dbg_backtrace                         false
% 59.80/8.02  --dbg_dump_prop_clauses                 false
% 59.80/8.02  --dbg_dump_prop_clauses_file            -
% 59.80/8.02  --dbg_out_stat                          false
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  ------ Proving...
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  % SZS status Theorem for theBenchmark.p
% 59.80/8.02  
% 59.80/8.02  % SZS output start CNFRefutation for theBenchmark.p
% 59.80/8.02  
% 59.80/8.02  fof(f9,axiom,(
% 59.80/8.02    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f30,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 59.80/8.02    inference(cnf_transformation,[],[f9])).
% 59.80/8.02  
% 59.80/8.02  fof(f1,axiom,(
% 59.80/8.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f21,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 59.80/8.02    inference(cnf_transformation,[],[f1])).
% 59.80/8.02  
% 59.80/8.02  fof(f12,conjecture,(
% 59.80/8.02    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f13,negated_conjecture,(
% 59.80/8.02    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 59.80/8.02    inference(negated_conjecture,[],[f12])).
% 59.80/8.02  
% 59.80/8.02  fof(f16,plain,(
% 59.80/8.02    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 59.80/8.02    inference(ennf_transformation,[],[f13])).
% 59.80/8.02  
% 59.80/8.02  fof(f17,plain,(
% 59.80/8.02    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 59.80/8.02    inference(flattening,[],[f16])).
% 59.80/8.02  
% 59.80/8.02  fof(f19,plain,(
% 59.80/8.02    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 59.80/8.02    introduced(choice_axiom,[])).
% 59.80/8.02  
% 59.80/8.02  fof(f20,plain,(
% 59.80/8.02    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 59.80/8.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 59.80/8.02  
% 59.80/8.02  fof(f33,plain,(
% 59.80/8.02    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 59.80/8.02    inference(cnf_transformation,[],[f20])).
% 59.80/8.02  
% 59.80/8.02  fof(f8,axiom,(
% 59.80/8.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f29,plain,(
% 59.80/8.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 59.80/8.02    inference(cnf_transformation,[],[f8])).
% 59.80/8.02  
% 59.80/8.02  fof(f6,axiom,(
% 59.80/8.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f27,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 59.80/8.02    inference(cnf_transformation,[],[f6])).
% 59.80/8.02  
% 59.80/8.02  fof(f11,axiom,(
% 59.80/8.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f32,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 59.80/8.02    inference(cnf_transformation,[],[f11])).
% 59.80/8.02  
% 59.80/8.02  fof(f10,axiom,(
% 59.80/8.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f31,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.80/8.02    inference(cnf_transformation,[],[f10])).
% 59.80/8.02  
% 59.80/8.02  fof(f40,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 59.80/8.02    inference(definition_unfolding,[],[f32,f31])).
% 59.80/8.02  
% 59.80/8.02  fof(f7,axiom,(
% 59.80/8.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f28,plain,(
% 59.80/8.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.80/8.02    inference(cnf_transformation,[],[f7])).
% 59.80/8.02  
% 59.80/8.02  fof(f35,plain,(
% 59.80/8.02    r1_xboole_0(sK3,sK1)),
% 59.80/8.02    inference(cnf_transformation,[],[f20])).
% 59.80/8.02  
% 59.80/8.02  fof(f3,axiom,(
% 59.80/8.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f14,plain,(
% 59.80/8.02    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 59.80/8.02    inference(ennf_transformation,[],[f3])).
% 59.80/8.02  
% 59.80/8.02  fof(f24,plain,(
% 59.80/8.02    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 59.80/8.02    inference(cnf_transformation,[],[f14])).
% 59.80/8.02  
% 59.80/8.02  fof(f2,axiom,(
% 59.80/8.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f18,plain,(
% 59.80/8.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 59.80/8.02    inference(nnf_transformation,[],[f2])).
% 59.80/8.02  
% 59.80/8.02  fof(f22,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 59.80/8.02    inference(cnf_transformation,[],[f18])).
% 59.80/8.02  
% 59.80/8.02  fof(f38,plain,(
% 59.80/8.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 59.80/8.02    inference(definition_unfolding,[],[f22,f31])).
% 59.80/8.02  
% 59.80/8.02  fof(f4,axiom,(
% 59.80/8.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f25,plain,(
% 59.80/8.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 59.80/8.02    inference(cnf_transformation,[],[f4])).
% 59.80/8.02  
% 59.80/8.02  fof(f39,plain,(
% 59.80/8.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 59.80/8.02    inference(definition_unfolding,[],[f25,f31])).
% 59.80/8.02  
% 59.80/8.02  fof(f34,plain,(
% 59.80/8.02    r1_xboole_0(sK2,sK0)),
% 59.80/8.02    inference(cnf_transformation,[],[f20])).
% 59.80/8.02  
% 59.80/8.02  fof(f5,axiom,(
% 59.80/8.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 59.80/8.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.80/8.02  
% 59.80/8.02  fof(f15,plain,(
% 59.80/8.02    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 59.80/8.02    inference(ennf_transformation,[],[f5])).
% 59.80/8.02  
% 59.80/8.02  fof(f26,plain,(
% 59.80/8.02    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 59.80/8.02    inference(cnf_transformation,[],[f15])).
% 59.80/8.02  
% 59.80/8.02  fof(f36,plain,(
% 59.80/8.02    sK1 != sK2),
% 59.80/8.02    inference(cnf_transformation,[],[f20])).
% 59.80/8.02  
% 59.80/8.02  cnf(c_100,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_276,plain,
% 59.80/8.02      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 59.80/8.02      inference(instantiation,[status(thm)],[c_100]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_212937,plain,
% 59.80/8.02      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 59.80/8.02      inference(instantiation,[status(thm)],[c_276]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_9,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.80/8.02      inference(cnf_transformation,[],[f30]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_0,plain,
% 59.80/8.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(cnf_transformation,[],[f21]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_14,negated_conjecture,
% 59.80/8.02      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 59.80/8.02      inference(cnf_transformation,[],[f33]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_458,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_0,c_14]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_8,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(cnf_transformation,[],[f29]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_6,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(cnf_transformation,[],[f27]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_616,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3181,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK3,k4_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_458,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3613,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_9,c_3181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_10,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 59.80/8.02      inference(cnf_transformation,[],[f40]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_680,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_7,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.80/8.02      inference(cnf_transformation,[],[f28]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_685,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_680,c_7]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3645,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3613,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_530,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1172,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_10,c_530]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3171,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1172,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3214,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_3171,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3215,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3214,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_15919,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_3215]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_37814,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_6,c_15919]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_186078,plain,
% 59.80/8.02      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK1),sK3)) = sK2 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3645,c_37814]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_12,negated_conjecture,
% 59.80/8.02      ( r1_xboole_0(sK3,sK1) ),
% 59.80/8.02      inference(cnf_transformation,[],[f35]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_263,plain,
% 59.80/8.02      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 59.80/8.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3,plain,
% 59.80/8.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 59.80/8.02      inference(cnf_transformation,[],[f24]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_264,plain,
% 59.80/8.02      ( r1_xboole_0(X0,X1) != iProver_top
% 59.80/8.02      | r1_xboole_0(X1,X0) = iProver_top ),
% 59.80/8.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_526,plain,
% 59.80/8.02      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_263,c_264]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2,plain,
% 59.80/8.02      ( ~ r1_xboole_0(X0,X1)
% 59.80/8.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 59.80/8.02      inference(cnf_transformation,[],[f38]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_265,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 59.80/8.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 59.80/8.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1013,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_526,c_265]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1346,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1013,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_603,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2410,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_603,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2413,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_2410]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3436,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1346,c_2413]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1772,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1172,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1774,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_1772,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3464,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3436,c_685,c_1774]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_532,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_458,c_9]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_750,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_532,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_4,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 59.80/8.02      inference(cnf_transformation,[],[f39]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_267,plain,
% 59.80/8.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_4,c_7]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_613,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_267,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_621,plain,
% 59.80/8.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_613,c_9]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_753,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_750,c_621]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_834,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_753,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_835,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_834,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_15969,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X0),X1)) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_10,c_3215]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_38742,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2)) = sK3 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_15969,c_3181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_614,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_620,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_614,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5439,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK0),X1)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_458,c_620]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5527,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,X1))) = k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_5439,c_620]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_39009,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),sK3),sK2)))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_38742,c_5527]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_39010,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X1),sK3),sK2)))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_39009,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1769,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1172,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1775,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1769,c_8,c_621]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2636,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_1775]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_4676,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2636,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_39536,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_39010,c_4676]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3177,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62402,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2),sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_39536,c_3177]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_833,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_753,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_836,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_833,c_620,c_621]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1004,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_836,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1005,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1),sK2) = k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1004,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16060,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3215,c_5527]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16066,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_16060,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16833,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X1,sK3),k2_xboole_0(X2,X1))),X0),k2_xboole_0(sK1,sK0))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_16066,c_3215]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_32502,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X1,X0))),sK3),sK2)) = sK3 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_16833,c_3181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_32889,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2)) = sK3 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_458,c_32502]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_33166,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),sK3) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_32889,c_2413]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_33226,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),sK3) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_33166,c_32889]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_40418,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),X1))),sK3),sK2),sK3) = sK3 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1005,c_33226]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_612,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_622,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_612,c_620,c_621]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1173,plain,
% 59.80/8.02      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_458,c_530]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3172,plain,
% 59.80/8.02      ( k2_xboole_0(sK0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1173,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1011,plain,
% 59.80/8.02      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_263,c_265]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1272,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1011,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1273,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k4_xboole_0(sK3,sK1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1272,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2037,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1273,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2038,plain,
% 59.80/8.02      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_2037,c_1774]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3212,plain,
% 59.80/8.02      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_3172,c_2038]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3213,plain,
% 59.80/8.02      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3212,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_13,negated_conjecture,
% 59.80/8.02      ( r1_xboole_0(sK2,sK0) ),
% 59.80/8.02      inference(cnf_transformation,[],[f34]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_262,plain,
% 59.80/8.02      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 59.80/8.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_527,plain,
% 59.80/8.02      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_262,c_264]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1014,plain,
% 59.80/8.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_527,c_265]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1395,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = sK0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1014,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3437,plain,
% 59.80/8.02      ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1395,c_2413]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3463,plain,
% 59.80/8.02      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3437,c_685,c_1774]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_40495,plain,
% 59.80/8.02      ( sK0 = sK3 ),
% 59.80/8.02      inference(demodulation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_40418,c_622,c_685,c_3213,c_3463]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62871,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK2),sK3)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_62402,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62872,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),k2_xboole_0(sK2,sK3))) = sK1 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_62871,c_8,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62873,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),k2_xboole_0(sK1,sK0))) = sK1 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_62872,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62874,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK3)) = sK1 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_62873,c_3177,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1171,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_6,c_530]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2491,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1171,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2497,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_2491,c_8,c_621]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_14510,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X0),X2))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2497,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_34181,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)),k2_xboole_0(X1,k2_xboole_0(X1,X3))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3215,c_14510]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2431,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2410,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_34286,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X3))) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_34181,c_8,c_2431]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_179749,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(X0,sK1),k2_xboole_0(k2_xboole_0(X1,X0),sK1)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_62874,c_34286]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_180468,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),sK1)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_835,c_179749]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_4897,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),sK3) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3645,c_2636]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_4900,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_4897,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_7480,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_4900]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_9363,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_7480]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_11620,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),sK1) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_9363,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_11629,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),sK1) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_11620,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2493,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1171,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2496,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_2493,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3619,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1172,c_3181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3638,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3619,c_8,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16339,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3638,c_5527]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16340,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_16339,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_17003,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,sK2))),X0),k2_xboole_0(sK1,sK0))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_16340,c_3215]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_44205,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X1,sK2))),X0),k2_xboole_0(sK1,sK3))) = X0 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_17003,c_17003,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91954,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k2_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2496,c_44205]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_678,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_7,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_687,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_678,c_267]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_44287,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k1_xboole_0),k2_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_44205,c_687]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_44384,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),k2_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_44287,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91966,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_91954,c_44384]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91967,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_91966,c_8,c_620,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91968,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) = k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_91967,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91969,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_91968,c_530,c_620,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3179,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_6,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_117906,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(k2_xboole_0(X0,sK2),sK3)),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK2),sK3))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)))) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_91969,c_3179]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_94256,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_91969,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_91570,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2410,c_2496]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1180,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_530,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1182,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1180,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41004,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2413,c_1182]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41220,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_41004,c_1182]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_92363,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_91570,c_9,c_41220]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_94307,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),sK3),k2_xboole_0(sK1,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_94256,c_92363]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118797,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,sK2),sK3))) ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_117906,c_91969,c_94307]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_92552,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X2,X1))) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_92363,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_679,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_686,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_679,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_10509,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_686,c_3177]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_10654,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,X1))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2410,c_10509]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3482,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_10,c_2431]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3517,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_3482,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5910,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_8,c_3517]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3446,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2413,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5845,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_10,c_3446]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_683,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5892,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_5845,c_683]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5977,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_5910,c_8,c_5892]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5978,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_5977,c_3177]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_10747,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_10654,c_620,c_5978]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1181,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_530,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_10748,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_10747,c_1181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_92637,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_92552,c_10748]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118798,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK2,sK3))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_118797,c_620,c_92637]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118799,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_118798,c_458]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118800,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK3))) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_118799,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3442,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2413,c_9]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_122038,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK3),X0),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_118800,c_3442]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5,plain,
% 59.80/8.02      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 59.80/8.02      inference(cnf_transformation,[],[f26]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_167166,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK3),X0)) != k1_xboole_0
% 59.80/8.02      | k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_122038,c_5]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_15994,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK0)),X0),k2_xboole_0(sK3,k4_xboole_0(X1,sK2)))) = X0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3181,c_3215]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_71257,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,k4_xboole_0(X0,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1774,c_15994]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3628,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,k4_xboole_0(X0,sK2))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3181,c_530]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_71284,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK3)),X1),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK3)),X1) ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_71257,c_3628,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_71285,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK3),X1)) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_71284,c_8,c_620,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_33188,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))),sK3),sK2),k2_xboole_0(X1,sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_32889,c_4676]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_45673,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2))),sK3),sK2),k2_xboole_0(X1,sK3)) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_33188,c_33188,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_45674,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k2_xboole_0(sK2,k2_xboole_0(X1,sK3))) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_45673,c_8,c_41220]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_117881,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3),k2_xboole_0(sK2,k2_xboole_0(X1,sK3))),k4_xboole_0(X2,k2_xboole_0(sK2,k2_xboole_0(X1,sK3)))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(X1,sK3)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3)))) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_45674,c_3179]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41042,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1182,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3614,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_267,c_3181]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3644,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3614,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2660,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1775,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2662,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_2660,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_101517,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_2662]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_102802,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_101517,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_104243,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),X0),sK3) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3644,c_102802]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5155,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(sK1,sK0),sK2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3644,c_2413]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5166,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),sK2),sK3) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_5155,c_3644]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_104558,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),sK2),X0),sK3) = sK3 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_104243,c_5166,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_104559,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,X0)),sK3) = sK3 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_104558,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_104724,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(X0,sK2)),sK3) = sK3 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_41042,c_104559]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118854,plain,
% 59.80/8.02      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(X1,sK3)),sK3))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X1,sK3)))) ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_117881,c_45674,c_104724]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_16832,plain,
% 59.80/8.02      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(X1,X0)),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_16066,c_4676]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_17299,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_16832,c_8]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_109932,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_17299,c_17299,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5952,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_3517,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_5958,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_5952,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_110102,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,sK3),k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,sK3),k1_xboole_0))) = k2_xboole_0(k2_xboole_0(X0,sK3),X1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_109932,c_5958]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3501,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_2431,c_616]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_3509,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_3501,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_68905,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),X2) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1182,c_3509]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_69658,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_68905,c_2413]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_68899,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) = k2_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_683,c_3509]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_69673,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_68899,c_683]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_110161,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(X0,sK3),X1) = k2_xboole_0(k2_xboole_0(sK3,X0),X1) ),
% 59.80/8.02      inference(demodulation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_110102,c_7,c_69658,c_69673]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_110992,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,sK3),X2)) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,X2))) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_110161,c_620]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_110662,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X1,sK3)) = k2_xboole_0(k2_xboole_0(sK3,X1),X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_110161,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_113690,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,X1),k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X2,k2_xboole_0(X1,sK3)),X3)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_110662,c_620]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_110723,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,X2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,X1),X2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_110161,c_620]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_114015,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,sK3)),X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(sK3,k2_xboole_0(X1,X3)))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_113690,c_620,c_110723]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118855,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)),X1)) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 59.80/8.02      inference(demodulation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_118854,c_92637,c_110992,c_114015]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1339,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1173,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1340,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1339,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2311,plain,
% 59.80/8.02      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1340,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118856,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK0),X1)) ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_118855,c_458,c_2311]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_118857,plain,
% 59.80/8.02      ( k4_xboole_0(X0,k2_xboole_0(sK1,k2_xboole_0(sK3,X1))) = k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_118856,c_620,c_40495]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_123256,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_118857,c_267]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_167223,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2))
% 59.80/8.02      | k1_xboole_0 != k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_167166,c_71285,c_123256]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_167224,plain,
% 59.80/8.02      ( k2_xboole_0(k2_xboole_0(sK1,sK3),X0) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(equality_resolution_simp,[status(thm)],[c_167223]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_180784,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_180468,c_11629,c_40495,c_167224]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_176629,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK1,k2_xboole_0(sK3,X0)),k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) != k1_xboole_0
% 59.80/8.02      | k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_123256,c_5]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_176689,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2))
% 59.80/8.02      | k1_xboole_0 != k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_176629,c_267,c_118857]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_176690,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 59.80/8.02      inference(equality_resolution_simp,[status(thm)],[c_176689]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_180785,plain,
% 59.80/8.02      ( k4_xboole_0(k2_xboole_0(sK2,sK1),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k1_xboole_0 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_180784,c_118857,c_176690]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_180970,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0),k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_180785,c_10]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41358,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_0,c_41042]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41598,plain,
% 59.80/8.02      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_6,c_41358]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_41842,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_41598,c_41358]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_181050,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
% 59.80/8.02      inference(demodulation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_180970,c_7,c_41842,c_92363]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_62297,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_532,c_3177]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1012,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_262,c_265]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1281,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1012,c_6]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1282,plain,
% 59.80/8.02      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k4_xboole_0(sK2,sK0) ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_1281,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2046,plain,
% 59.80/8.02      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
% 59.80/8.02      inference(superposition,[status(thm)],[c_1282,c_0]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2047,plain,
% 59.80/8.02      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_2046,c_1774]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_63025,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_62297,c_2047]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_63026,plain,
% 59.80/8.02      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 59.80/8.02      inference(demodulation,[status(thm)],[c_63025,c_685]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_181051,plain,
% 59.80/8.02      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 59.80/8.02      inference(light_normalisation,[status(thm)],[c_181050,c_63026]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_187365,plain,
% 59.80/8.02      ( sK2 = sK1 ),
% 59.80/8.02      inference(light_normalisation,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_186078,c_3464,c_181051]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_99,plain,( X0 = X0 ),theory(equality) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_2383,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
% 59.80/8.02      inference(instantiation,[status(thm)],[c_99]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_552,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,X0) != k4_xboole_0(X0,sK1) | sK1 = X0 ),
% 59.80/8.02      inference(instantiation,[status(thm)],[c_5]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_1117,plain,
% 59.80/8.02      ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1) | sK1 = sK1 ),
% 59.80/8.02      inference(instantiation,[status(thm)],[c_552]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(c_11,negated_conjecture,
% 59.80/8.02      ( sK1 != sK2 ),
% 59.80/8.02      inference(cnf_transformation,[],[f36]) ).
% 59.80/8.02  
% 59.80/8.02  cnf(contradiction,plain,
% 59.80/8.02      ( $false ),
% 59.80/8.02      inference(minisat,
% 59.80/8.02                [status(thm)],
% 59.80/8.02                [c_212937,c_187365,c_2383,c_1117,c_11]) ).
% 59.80/8.02  
% 59.80/8.02  
% 59.80/8.02  % SZS output end CNFRefutation for theBenchmark.p
% 59.80/8.02  
% 59.80/8.02  ------                               Statistics
% 59.80/8.02  
% 59.80/8.02  ------ General
% 59.80/8.02  
% 59.80/8.02  abstr_ref_over_cycles:                  0
% 59.80/8.02  abstr_ref_under_cycles:                 0
% 59.80/8.02  gc_basic_clause_elim:                   0
% 59.80/8.02  forced_gc_time:                         0
% 59.80/8.02  parsing_time:                           0.009
% 59.80/8.02  unif_index_cands_time:                  0.
% 59.80/8.02  unif_index_add_time:                    0.
% 59.80/8.02  orderings_time:                         0.
% 59.80/8.02  out_proof_time:                         0.017
% 59.80/8.02  total_time:                             7.242
% 59.80/8.02  num_of_symbols:                         39
% 59.80/8.02  num_of_terms:                           384174
% 59.80/8.02  
% 59.80/8.02  ------ Preprocessing
% 59.80/8.02  
% 59.80/8.02  num_of_splits:                          0
% 59.80/8.02  num_of_split_atoms:                     0
% 59.80/8.02  num_of_reused_defs:                     0
% 59.80/8.02  num_eq_ax_congr_red:                    0
% 59.80/8.02  num_of_sem_filtered_clauses:            1
% 59.80/8.02  num_of_subtypes:                        0
% 59.80/8.02  monotx_restored_types:                  0
% 59.80/8.02  sat_num_of_epr_types:                   0
% 59.80/8.02  sat_num_of_non_cyclic_types:            0
% 59.80/8.02  sat_guarded_non_collapsed_types:        0
% 59.80/8.02  num_pure_diseq_elim:                    0
% 59.80/8.02  simp_replaced_by:                       0
% 59.80/8.02  res_preprocessed:                       56
% 59.80/8.02  prep_upred:                             0
% 59.80/8.02  prep_unflattend:                        0
% 59.80/8.02  smt_new_axioms:                         0
% 59.80/8.02  pred_elim_cands:                        1
% 59.80/8.02  pred_elim:                              0
% 59.80/8.02  pred_elim_cl:                           0
% 59.80/8.02  pred_elim_cycles:                       1
% 59.80/8.02  merged_defs:                            6
% 59.80/8.02  merged_defs_ncl:                        0
% 59.80/8.02  bin_hyper_res:                          6
% 59.80/8.02  prep_cycles:                            3
% 59.80/8.02  pred_elim_time:                         0.
% 59.80/8.02  splitting_time:                         0.
% 59.80/8.02  sem_filter_time:                        0.
% 59.80/8.02  monotx_time:                            0.
% 59.80/8.02  subtype_inf_time:                       0.
% 59.80/8.02  
% 59.80/8.02  ------ Problem properties
% 59.80/8.02  
% 59.80/8.02  clauses:                                15
% 59.80/8.02  conjectures:                            4
% 59.80/8.02  epr:                                    4
% 59.80/8.02  horn:                                   15
% 59.80/8.02  ground:                                 4
% 59.80/8.02  unary:                                  11
% 59.80/8.02  binary:                                 4
% 59.80/8.02  lits:                                   19
% 59.80/8.02  lits_eq:                                13
% 59.80/8.02  fd_pure:                                0
% 59.80/8.02  fd_pseudo:                              0
% 59.80/8.02  fd_cond:                                0
% 59.80/8.02  fd_pseudo_cond:                         1
% 59.80/8.02  ac_symbols:                             0
% 59.80/8.02  
% 59.80/8.02  ------ Propositional Solver
% 59.80/8.02  
% 59.80/8.02  prop_solver_calls:                      45
% 59.80/8.02  prop_fast_solver_calls:                 1223
% 59.80/8.02  smt_solver_calls:                       0
% 59.80/8.02  smt_fast_solver_calls:                  0
% 59.80/8.02  prop_num_of_clauses:                    43283
% 59.80/8.02  prop_preprocess_simplified:             34010
% 59.80/8.02  prop_fo_subsumed:                       1
% 59.80/8.03  prop_solver_time:                       0.
% 59.80/8.03  smt_solver_time:                        0.
% 59.80/8.03  smt_fast_solver_time:                   0.
% 59.80/8.03  prop_fast_solver_time:                  0.
% 59.80/8.03  prop_unsat_core_time:                   0.004
% 59.80/8.03  
% 59.80/8.03  ------ QBF
% 59.80/8.03  
% 59.80/8.03  qbf_q_res:                              0
% 59.80/8.03  qbf_num_tautologies:                    0
% 59.80/8.03  qbf_prep_cycles:                        0
% 59.80/8.03  
% 59.80/8.03  ------ BMC1
% 59.80/8.03  
% 59.80/8.03  bmc1_current_bound:                     -1
% 59.80/8.03  bmc1_last_solved_bound:                 -1
% 59.80/8.03  bmc1_unsat_core_size:                   -1
% 59.80/8.03  bmc1_unsat_core_parents_size:           -1
% 59.80/8.03  bmc1_merge_next_fun:                    0
% 59.80/8.03  bmc1_unsat_core_clauses_time:           0.
% 59.80/8.03  
% 59.80/8.03  ------ Instantiation
% 59.80/8.03  
% 59.80/8.03  inst_num_of_clauses:                    8860
% 59.80/8.03  inst_num_in_passive:                    4964
% 59.80/8.03  inst_num_in_active:                     2329
% 59.80/8.03  inst_num_in_unprocessed:                1573
% 59.80/8.03  inst_num_of_loops:                      2610
% 59.80/8.03  inst_num_of_learning_restarts:          0
% 59.80/8.03  inst_num_moves_active_passive:          278
% 59.80/8.03  inst_lit_activity:                      0
% 59.80/8.03  inst_lit_activity_moves:                1
% 59.80/8.03  inst_num_tautologies:                   0
% 59.80/8.03  inst_num_prop_implied:                  0
% 59.80/8.03  inst_num_existing_simplified:           0
% 59.80/8.03  inst_num_eq_res_simplified:             0
% 59.80/8.03  inst_num_child_elim:                    0
% 59.80/8.03  inst_num_of_dismatching_blockings:      17731
% 59.80/8.03  inst_num_of_non_proper_insts:           16623
% 59.80/8.03  inst_num_of_duplicates:                 0
% 59.80/8.03  inst_inst_num_from_inst_to_res:         0
% 59.80/8.03  inst_dismatching_checking_time:         0.
% 59.80/8.03  
% 59.80/8.03  ------ Resolution
% 59.80/8.03  
% 59.80/8.03  res_num_of_clauses:                     0
% 59.80/8.03  res_num_in_passive:                     0
% 59.80/8.03  res_num_in_active:                      0
% 59.80/8.03  res_num_of_loops:                       59
% 59.80/8.03  res_forward_subset_subsumed:            1354
% 59.80/8.03  res_backward_subset_subsumed:           22
% 59.80/8.03  res_forward_subsumed:                   0
% 59.80/8.03  res_backward_subsumed:                  0
% 59.80/8.03  res_forward_subsumption_resolution:     0
% 59.80/8.03  res_backward_subsumption_resolution:    0
% 59.80/8.03  res_clause_to_clause_subsumption:       330626
% 59.80/8.03  res_orphan_elimination:                 0
% 59.80/8.03  res_tautology_del:                      973
% 59.80/8.03  res_num_eq_res_simplified:              0
% 59.80/8.03  res_num_sel_changes:                    0
% 59.80/8.03  res_moves_from_active_to_pass:          0
% 59.80/8.03  
% 59.80/8.03  ------ Superposition
% 59.80/8.03  
% 59.80/8.03  sup_time_total:                         0.
% 59.80/8.03  sup_time_generating:                    0.
% 59.80/8.03  sup_time_sim_full:                      0.
% 59.80/8.03  sup_time_sim_immed:                     0.
% 59.80/8.03  
% 59.80/8.03  sup_num_of_clauses:                     13943
% 59.80/8.03  sup_num_in_active:                      413
% 59.80/8.03  sup_num_in_passive:                     13530
% 59.80/8.03  sup_num_of_loops:                       520
% 59.80/8.03  sup_fw_superposition:                   46872
% 59.80/8.03  sup_bw_superposition:                   36644
% 59.80/8.03  sup_immediate_simplified:               46533
% 59.80/8.03  sup_given_eliminated:                   34
% 59.80/8.03  comparisons_done:                       0
% 59.80/8.03  comparisons_avoided:                    0
% 59.80/8.03  
% 59.80/8.03  ------ Simplifications
% 59.80/8.03  
% 59.80/8.03  
% 59.80/8.03  sim_fw_subset_subsumed:                 34
% 59.80/8.03  sim_bw_subset_subsumed:                 24
% 59.80/8.03  sim_fw_subsumed:                        11191
% 59.80/8.03  sim_bw_subsumed:                        546
% 59.80/8.03  sim_fw_subsumption_res:                 0
% 59.80/8.03  sim_bw_subsumption_res:                 0
% 59.80/8.03  sim_tautology_del:                      1049
% 59.80/8.03  sim_eq_tautology_del:                   15460
% 59.80/8.03  sim_eq_res_simp:                        97
% 59.80/8.03  sim_fw_demodulated:                     33698
% 59.80/8.03  sim_bw_demodulated:                     809
% 59.80/8.03  sim_light_normalised:                   22542
% 59.80/8.03  sim_joinable_taut:                      0
% 59.80/8.03  sim_joinable_simp:                      0
% 59.80/8.03  sim_ac_normalised:                      0
% 59.80/8.03  sim_smt_subsumption:                    0
% 59.80/8.03  
%------------------------------------------------------------------------------
