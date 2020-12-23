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
% DateTime   : Thu Dec  3 11:24:16 EST 2020

% Result     : Theorem 35.20s
% Output     : CNFRefutation 35.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 169 expanded)
%              Number of clauses        :   48 (  63 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 341 expanded)
%              Number of equality atoms :   74 ( 160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f21,f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f26,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f25,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_96,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_99,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_143722,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_96,c_99])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_143828,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_143722,c_0])).

cnf(c_97,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_143733,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_97,c_96])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_143739,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_143733,c_2])).

cnf(c_143730,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_97,c_0])).

cnf(c_144212,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143739,c_143730])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_144220,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_144212,c_1])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_144290,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[status(thm)],[c_144220,c_6])).

cnf(c_144541,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(resolution,[status(thm)],[c_143828,c_144290])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_144838,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | r1_xboole_0(X0,sK0) ),
    inference(resolution,[status(thm)],[c_144541,c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_145107,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) ),
    inference(resolution,[status(thm)],[c_144838,c_3])).

cnf(c_145109,plain,
    ( ~ r1_tarski(sK0,sK2)
    | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(instantiation,[status(thm)],[c_145107])).

cnf(c_49163,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_140260,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_49163])).

cnf(c_140262,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_140260])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_28516,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0)
    | r1_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_28518,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
    | r1_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_28516])).

cnf(c_5562,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5180,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != X1
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_5203,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5180])).

cnf(c_5204,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5203])).

cnf(c_4491,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4140,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4034,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_4136,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_4034])).

cnf(c_3930,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_3981,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_4028,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_2096,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1206,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_1293,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_1294,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1293])).

cnf(c_1332,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_713,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_105,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_145109,c_140262,c_28518,c_5562,c_5204,c_4491,c_4140,c_4136,c_4028,c_2096,c_1332,c_713,c_105,c_6,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:56:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.20/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.20/4.99  
% 35.20/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.20/4.99  
% 35.20/4.99  ------  iProver source info
% 35.20/4.99  
% 35.20/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.20/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.20/4.99  git: non_committed_changes: false
% 35.20/4.99  git: last_make_outside_of_git: false
% 35.20/4.99  
% 35.20/4.99  ------ 
% 35.20/4.99  ------ Parsing...
% 35.20/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  ------ Proving...
% 35.20/4.99  ------ Problem Properties 
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  clauses                                 9
% 35.20/4.99  conjectures                             3
% 35.20/4.99  EPR                                     3
% 35.20/4.99  Horn                                    9
% 35.20/4.99  unary                                   4
% 35.20/4.99  binary                                  4
% 35.20/4.99  lits                                    15
% 35.20/4.99  lits eq                                 3
% 35.20/4.99  fd_pure                                 0
% 35.20/4.99  fd_pseudo                               0
% 35.20/4.99  fd_cond                                 0
% 35.20/4.99  fd_pseudo_cond                          0
% 35.20/4.99  AC symbols                              0
% 35.20/4.99  
% 35.20/4.99  ------ Input Options Time Limit: Unbounded
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing...
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.20/4.99  Current options:
% 35.20/4.99  ------ 
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing...
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.20/4.99  
% 35.20/4.99  ------ Proving...
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  % SZS status Theorem for theBenchmark.p
% 35.20/4.99  
% 35.20/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.20/4.99  
% 35.20/4.99  fof(f1,axiom,(
% 35.20/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f17,plain,(
% 35.20/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.20/4.99    inference(cnf_transformation,[],[f1])).
% 35.20/4.99  
% 35.20/4.99  fof(f4,axiom,(
% 35.20/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f21,plain,(
% 35.20/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.20/4.99    inference(cnf_transformation,[],[f4])).
% 35.20/4.99  
% 35.20/4.99  fof(f27,plain,(
% 35.20/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 35.20/4.99    inference(definition_unfolding,[],[f17,f21,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f2,axiom,(
% 35.20/4.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f14,plain,(
% 35.20/4.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.20/4.99    inference(nnf_transformation,[],[f2])).
% 35.20/4.99  
% 35.20/4.99  fof(f18,plain,(
% 35.20/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.20/4.99    inference(cnf_transformation,[],[f14])).
% 35.20/4.99  
% 35.20/4.99  fof(f29,plain,(
% 35.20/4.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.20/4.99    inference(definition_unfolding,[],[f18,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f19,plain,(
% 35.20/4.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.20/4.99    inference(cnf_transformation,[],[f14])).
% 35.20/4.99  
% 35.20/4.99  fof(f28,plain,(
% 35.20/4.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.20/4.99    inference(definition_unfolding,[],[f19,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f7,conjecture,(
% 35.20/4.99    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f8,negated_conjecture,(
% 35.20/4.99    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 35.20/4.99    inference(negated_conjecture,[],[f7])).
% 35.20/4.99  
% 35.20/4.99  fof(f13,plain,(
% 35.20/4.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 35.20/4.99    inference(ennf_transformation,[],[f8])).
% 35.20/4.99  
% 35.20/4.99  fof(f15,plain,(
% 35.20/4.99    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 35.20/4.99    introduced(choice_axiom,[])).
% 35.20/4.99  
% 35.20/4.99  fof(f16,plain,(
% 35.20/4.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 35.20/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 35.20/4.99  
% 35.20/4.99  fof(f26,plain,(
% 35.20/4.99    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 35.20/4.99    inference(cnf_transformation,[],[f16])).
% 35.20/4.99  
% 35.20/4.99  fof(f32,plain,(
% 35.20/4.99    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 35.20/4.99    inference(definition_unfolding,[],[f26,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f5,axiom,(
% 35.20/4.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f10,plain,(
% 35.20/4.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 35.20/4.99    inference(ennf_transformation,[],[f5])).
% 35.20/4.99  
% 35.20/4.99  fof(f11,plain,(
% 35.20/4.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 35.20/4.99    inference(flattening,[],[f10])).
% 35.20/4.99  
% 35.20/4.99  fof(f22,plain,(
% 35.20/4.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 35.20/4.99    inference(cnf_transformation,[],[f11])).
% 35.20/4.99  
% 35.20/4.99  fof(f3,axiom,(
% 35.20/4.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f9,plain,(
% 35.20/4.99    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 35.20/4.99    inference(ennf_transformation,[],[f3])).
% 35.20/4.99  
% 35.20/4.99  fof(f20,plain,(
% 35.20/4.99    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 35.20/4.99    inference(cnf_transformation,[],[f9])).
% 35.20/4.99  
% 35.20/4.99  fof(f30,plain,(
% 35.20/4.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 35.20/4.99    inference(definition_unfolding,[],[f20,f21,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f6,axiom,(
% 35.20/4.99    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 35.20/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.20/4.99  
% 35.20/4.99  fof(f12,plain,(
% 35.20/4.99    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 35.20/4.99    inference(ennf_transformation,[],[f6])).
% 35.20/4.99  
% 35.20/4.99  fof(f23,plain,(
% 35.20/4.99    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 35.20/4.99    inference(cnf_transformation,[],[f12])).
% 35.20/4.99  
% 35.20/4.99  fof(f31,plain,(
% 35.20/4.99    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 35.20/4.99    inference(definition_unfolding,[],[f23,f21])).
% 35.20/4.99  
% 35.20/4.99  fof(f25,plain,(
% 35.20/4.99    r1_tarski(sK0,sK2)),
% 35.20/4.99    inference(cnf_transformation,[],[f16])).
% 35.20/4.99  
% 35.20/4.99  fof(f24,plain,(
% 35.20/4.99    ~r1_xboole_0(sK0,sK1)),
% 35.20/4.99    inference(cnf_transformation,[],[f16])).
% 35.20/4.99  
% 35.20/4.99  cnf(c_96,plain,( X0 = X0 ),theory(equality) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_99,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.20/4.99      theory(equality) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_143722,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_96,c_99]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_0,plain,
% 35.20/4.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 35.20/4.99      inference(cnf_transformation,[],[f27]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_143828,plain,
% 35.20/4.99      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 35.20/4.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_143722,c_0]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_97,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_143733,plain,
% 35.20/4.99      ( X0 != X1 | X1 = X0 ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_97,c_96]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_2,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.20/4.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.20/4.99      inference(cnf_transformation,[],[f29]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_143739,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.20/4.99      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_143733,c_2]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_143730,plain,
% 35.20/4.99      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 35.20/4.99      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_97,c_0]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_144212,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.20/4.99      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_143739,c_143730]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_1,plain,
% 35.20/4.99      ( r1_xboole_0(X0,X1)
% 35.20/4.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.20/4.99      inference(cnf_transformation,[],[f28]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_144220,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_144212,c_1]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_6,negated_conjecture,
% 35.20/4.99      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 35.20/4.99      inference(cnf_transformation,[],[f32]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_144290,plain,
% 35.20/4.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_144220,c_6]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_144541,plain,
% 35.20/4.99      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_143828,c_144290]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4,plain,
% 35.20/4.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 35.20/4.99      inference(cnf_transformation,[],[f22]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_144838,plain,
% 35.20/4.99      ( ~ r1_tarski(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
% 35.20/4.99      | r1_xboole_0(X0,sK0) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_144541,c_4]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_3,plain,
% 35.20/4.99      ( ~ r1_tarski(X0,X1)
% 35.20/4.99      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 35.20/4.99      inference(cnf_transformation,[],[f30]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_145107,plain,
% 35.20/4.99      ( ~ r1_tarski(X0,sK2)
% 35.20/4.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) ),
% 35.20/4.99      inference(resolution,[status(thm)],[c_144838,c_3]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_145109,plain,
% 35.20/4.99      ( ~ r1_tarski(sK0,sK2)
% 35.20/4.99      | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_145107]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_49163,plain,
% 35.20/4.99      ( ~ r1_xboole_0(X0,X1)
% 35.20/4.99      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != X0
% 35.20/4.99      | sK0 != X1 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_99]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_140260,plain,
% 35.20/4.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
% 35.20/4.99      | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
% 35.20/4.99      | sK0 != X0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_49163]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_140262,plain,
% 35.20/4.99      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
% 35.20/4.99      | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
% 35.20/4.99      | sK0 != sK0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_140260]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_5,plain,
% 35.20/4.99      ( r1_xboole_0(X0,X1)
% 35.20/4.99      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 35.20/4.99      inference(cnf_transformation,[],[f31]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_28516,plain,
% 35.20/4.99      ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0)
% 35.20/4.99      | r1_xboole_0(sK1,X0) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_28518,plain,
% 35.20/4.99      ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
% 35.20/4.99      | r1_xboole_0(sK1,sK0) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_28516]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_5562,plain,
% 35.20/4.99      ( ~ r1_xboole_0(sK1,sK0)
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_5180,plain,
% 35.20/4.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != X1
% 35.20/4.99      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != X1 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_97]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_5203,plain,
% 35.20/4.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 35.20/4.99      | k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
% 35.20/4.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_5180]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_5204,plain,
% 35.20/4.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k1_xboole_0
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_5203]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4491,plain,
% 35.20/4.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4140,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4034,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != X0
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_97]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4136,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_4034]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_3930,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 35.20/4.99      | k1_xboole_0 != X0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_97]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_3981,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 35.20/4.99      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_3930]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_4028,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 35.20/4.99      | k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_3981]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_2096,plain,
% 35.20/4.99      ( r1_xboole_0(sK0,sK1)
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_1]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_1206,plain,
% 35.20/4.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_97]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_1293,plain,
% 35.20/4.99      ( X0 != k1_xboole_0
% 35.20/4.99      | k1_xboole_0 = X0
% 35.20/4.99      | k1_xboole_0 != k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_1206]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_1294,plain,
% 35.20/4.99      ( X0 != k1_xboole_0 | k1_xboole_0 = X0 ),
% 35.20/4.99      inference(equality_resolution_simp,[status(thm)],[c_1293]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_1332,plain,
% 35.20/4.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
% 35.20/4.99      | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_1294]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_713,plain,
% 35.20/4.99      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 35.20/4.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_105,plain,
% 35.20/4.99      ( sK0 = sK0 ),
% 35.20/4.99      inference(instantiation,[status(thm)],[c_96]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_7,negated_conjecture,
% 35.20/4.99      ( r1_tarski(sK0,sK2) ),
% 35.20/4.99      inference(cnf_transformation,[],[f25]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(c_8,negated_conjecture,
% 35.20/4.99      ( ~ r1_xboole_0(sK0,sK1) ),
% 35.20/4.99      inference(cnf_transformation,[],[f24]) ).
% 35.20/4.99  
% 35.20/4.99  cnf(contradiction,plain,
% 35.20/4.99      ( $false ),
% 35.20/4.99      inference(minisat,
% 35.20/4.99                [status(thm)],
% 35.20/4.99                [c_145109,c_140262,c_28518,c_5562,c_5204,c_4491,c_4140,
% 35.20/4.99                 c_4136,c_4028,c_2096,c_1332,c_713,c_105,c_6,c_7,c_8]) ).
% 35.20/4.99  
% 35.20/4.99  
% 35.20/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.20/4.99  
% 35.20/4.99  ------                               Statistics
% 35.20/4.99  
% 35.20/4.99  ------ Selected
% 35.20/4.99  
% 35.20/4.99  total_time:                             4.325
% 35.20/4.99  
%------------------------------------------------------------------------------
