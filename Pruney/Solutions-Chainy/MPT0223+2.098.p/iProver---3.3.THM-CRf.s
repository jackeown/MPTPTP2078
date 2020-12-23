%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:01 EST 2020

% Result     : Theorem 19.05s
% Output     : CNFRefutation 19.05s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 293 expanded)
%              Number of clauses        :   66 ( 149 expanded)
%              Number of leaves         :   12 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  191 ( 598 expanded)
%              Number of equality atoms :  117 ( 481 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( sK0 != sK1
    & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f22,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_62,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_61,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_564,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_62,c_61])).

cnf(c_66,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_939,plain,
    ( X0 != X1
    | k1_tarski(X1) = k1_tarski(X0) ),
    inference(resolution,[status(thm)],[c_564,c_66])).

cnf(c_565,plain,
    ( X0 != X1
    | X2 != k1_tarski(X1)
    | k1_tarski(X0) = X2 ),
    inference(resolution,[status(thm)],[c_62,c_66])).

cnf(c_6429,plain,
    ( X0 != X1
    | X2 != X0
    | k1_tarski(X2) = k1_tarski(X1) ),
    inference(resolution,[status(thm)],[c_939,c_565])).

cnf(c_7,negated_conjecture,
    ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_935,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[status(thm)],[c_564,c_7])).

cnf(c_76566,plain,
    ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0
    | k1_tarski(k1_tarski(sK0)) = k1_tarski(X0) ),
    inference(resolution,[status(thm)],[c_6429,c_935])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_65,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_756,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r1_xboole_0(X1,k1_tarski(sK0))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_65,c_7])).

cnf(c_1247,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))
    | r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(resolution,[status(thm)],[c_756,c_935])).

cnf(c_1051,plain,
    ( k3_xboole_0(X0,k1_tarski(sK1)) = k3_xboole_0(X0,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_1720,plain,
    ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_986,plain,
    ( ~ r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | r1_xboole_0(X1,k1_tarski(sK0))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_935,c_65])).

cnf(c_760,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_65,c_61])).

cnf(c_962,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
    | ~ r1_xboole_0(k1_tarski(sK0),X0) ),
    inference(resolution,[status(thm)],[c_760,c_7])).

cnf(c_1897,plain,
    ( r1_xboole_0(X0,k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[status(thm)],[c_986,c_962])).

cnf(c_7360,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[status(thm)],[c_1897,c_935])).

cnf(c_1782,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k1_tarski(sK0))
    | X0 != X2
    | X1 != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_7176,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r1_xboole_0(X1,k1_tarski(sK0))
    | X0 != X1
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_31776,plain,
    ( ~ r1_xboole_0(X0,k1_tarski(sK0))
    | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_7176])).

cnf(c_1611,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2)
    | X1 != X2
    | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_4309,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
    | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X1)
    | X1 != X0
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_10964,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
    | ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(X1)))
    | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(X1))
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_4309])).

cnf(c_41333,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_10964])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_927,plain,
    ( X0 = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_564,c_0])).

cnf(c_6382,plain,
    ( X0 = X1
    | X1 != k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(resolution,[status(thm)],[c_927,c_62])).

cnf(c_562,plain,
    ( X0 != k1_tarski(sK0)
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = X0 ),
    inference(resolution,[status(thm)],[c_62,c_7])).

cnf(c_59699,plain,
    ( X0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | k2_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_tarski(sK0) ),
    inference(resolution,[status(thm)],[c_6382,c_562])).

cnf(c_555,plain,
    ( X0 != X1
    | k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X0 ),
    inference(resolution,[status(thm)],[c_62,c_0])).

cnf(c_2096,plain,
    ( X0 != X1
    | X2 != X0
    | k2_xboole_0(X1,k3_xboole_0(X1,X3)) = X2 ),
    inference(resolution,[status(thm)],[c_555,c_62])).

cnf(c_13326,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_tarski(sK0)
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
    inference(resolution,[status(thm)],[c_2096,c_935])).

cnf(c_61276,plain,
    ( X0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
    inference(resolution,[status(thm)],[c_59699,c_13326])).

cnf(c_6391,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,k2_xboole_0(X1,k3_xboole_0(X1,X3)))
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_927,c_65])).

cnf(c_2099,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | X1 != X3 ),
    inference(resolution,[status(thm)],[c_555,c_65])).

cnf(c_18665,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
    | ~ r1_xboole_0(X2,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_2099,c_7])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_19009,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
    | ~ r1_xboole_0(X2,k1_tarski(sK1))
    | X0 != k3_xboole_0(k1_tarski(sK0),X2) ),
    inference(resolution,[status(thm)],[c_18665,c_2])).

cnf(c_19378,plain,
    ( ~ r1_xboole_0(X0,k1_tarski(sK1))
    | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
    | k3_xboole_0(k1_tarski(sK0),X0) != k1_tarski(sK0) ),
    inference(resolution,[status(thm)],[c_19009,c_562])).

cnf(c_6,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_5,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_197,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_198,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_153,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_155,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_922,plain,
    ( X0 = X1
    | k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2) ),
    inference(superposition,[status(thm)],[c_153,c_155])).

cnf(c_1,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_378,plain,
    ( k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_383,plain,
    ( k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k1_tarski(sK0) ),
    inference(demodulation,[status(thm)],[c_378,c_0])).

cnf(c_3502,plain,
    ( k3_xboole_0(k1_tarski(sK0),X0) = k1_tarski(sK0)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_922,c_383])).

cnf(c_51512,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
    | ~ r1_xboole_0(X0,k1_tarski(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19378,c_6,c_9,c_12,c_198,c_3502])).

cnf(c_51513,plain,
    ( ~ r1_xboole_0(X0,k1_tarski(sK1))
    | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))) ),
    inference(renaming,[status(thm)],[c_51512])).

cnf(c_51534,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[status(thm)],[c_51513,c_962])).

cnf(c_224,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(sK1))
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_226,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK1 = sK0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_52272,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51534,c_6,c_9,c_12,c_198,c_226])).

cnf(c_76444,plain,
    ( r1_xboole_0(X0,k1_tarski(sK0))
    | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[status(thm)],[c_6391,c_52272])).

cnf(c_78216,plain,
    ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_76566,c_7,c_12,c_935,c_1247,c_1720,c_7360,c_31776,c_41333,c_61276,c_76444])).

cnf(c_78231,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_78216,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:56:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.05/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.05/3.00  
% 19.05/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.05/3.00  
% 19.05/3.00  ------  iProver source info
% 19.05/3.00  
% 19.05/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.05/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.05/3.00  git: non_committed_changes: false
% 19.05/3.00  git: last_make_outside_of_git: false
% 19.05/3.00  
% 19.05/3.00  ------ 
% 19.05/3.00  ------ Parsing...
% 19.05/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.05/3.00  
% 19.05/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.05/3.00  
% 19.05/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.05/3.00  
% 19.05/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.05/3.00  ------ Proving...
% 19.05/3.00  ------ Problem Properties 
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  clauses                                 8
% 19.05/3.00  conjectures                             2
% 19.05/3.00  EPR                                     1
% 19.05/3.00  Horn                                    7
% 19.05/3.00  unary                                   5
% 19.05/3.00  binary                                  3
% 19.05/3.00  lits                                    11
% 19.05/3.00  lits eq                                 6
% 19.05/3.00  fd_pure                                 0
% 19.05/3.00  fd_pseudo                               0
% 19.05/3.00  fd_cond                                 0
% 19.05/3.00  fd_pseudo_cond                          1
% 19.05/3.00  AC symbols                              0
% 19.05/3.00  
% 19.05/3.00  ------ Input Options Time Limit: Unbounded
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  ------ 
% 19.05/3.00  Current options:
% 19.05/3.00  ------ 
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  ------ Proving...
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  % SZS status Theorem for theBenchmark.p
% 19.05/3.00  
% 19.05/3.00   Resolution empty clause
% 19.05/3.00  
% 19.05/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.05/3.00  
% 19.05/3.00  fof(f7,conjecture,(
% 19.05/3.00    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f8,negated_conjecture,(
% 19.05/3.00    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 19.05/3.00    inference(negated_conjecture,[],[f7])).
% 19.05/3.00  
% 19.05/3.00  fof(f13,plain,(
% 19.05/3.00    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 19.05/3.00    inference(ennf_transformation,[],[f8])).
% 19.05/3.00  
% 19.05/3.00  fof(f14,plain,(
% 19.05/3.00    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK0 != sK1 & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0))),
% 19.05/3.00    introduced(choice_axiom,[])).
% 19.05/3.00  
% 19.05/3.00  fof(f15,plain,(
% 19.05/3.00    sK0 != sK1 & k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 19.05/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 19.05/3.00  
% 19.05/3.00  fof(f22,plain,(
% 19.05/3.00    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 19.05/3.00    inference(cnf_transformation,[],[f15])).
% 19.05/3.00  
% 19.05/3.00  fof(f5,axiom,(
% 19.05/3.00    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f11,plain,(
% 19.05/3.00    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 19.05/3.00    inference(ennf_transformation,[],[f5])).
% 19.05/3.00  
% 19.05/3.00  fof(f20,plain,(
% 19.05/3.00    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 19.05/3.00    inference(cnf_transformation,[],[f11])).
% 19.05/3.00  
% 19.05/3.00  fof(f24,plain,(
% 19.05/3.00    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 19.05/3.00    inference(equality_resolution,[],[f20])).
% 19.05/3.00  
% 19.05/3.00  fof(f1,axiom,(
% 19.05/3.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f16,plain,(
% 19.05/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 19.05/3.00    inference(cnf_transformation,[],[f1])).
% 19.05/3.00  
% 19.05/3.00  fof(f3,axiom,(
% 19.05/3.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f9,plain,(
% 19.05/3.00    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 19.05/3.00    inference(ennf_transformation,[],[f3])).
% 19.05/3.00  
% 19.05/3.00  fof(f18,plain,(
% 19.05/3.00    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) )),
% 19.05/3.00    inference(cnf_transformation,[],[f9])).
% 19.05/3.00  
% 19.05/3.00  fof(f23,plain,(
% 19.05/3.00    sK0 != sK1),
% 19.05/3.00    inference(cnf_transformation,[],[f15])).
% 19.05/3.00  
% 19.05/3.00  fof(f6,axiom,(
% 19.05/3.00    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f12,plain,(
% 19.05/3.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 19.05/3.00    inference(ennf_transformation,[],[f6])).
% 19.05/3.00  
% 19.05/3.00  fof(f21,plain,(
% 19.05/3.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 19.05/3.00    inference(cnf_transformation,[],[f12])).
% 19.05/3.00  
% 19.05/3.00  fof(f4,axiom,(
% 19.05/3.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f10,plain,(
% 19.05/3.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 19.05/3.00    inference(ennf_transformation,[],[f4])).
% 19.05/3.00  
% 19.05/3.00  fof(f19,plain,(
% 19.05/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 19.05/3.00    inference(cnf_transformation,[],[f10])).
% 19.05/3.00  
% 19.05/3.00  fof(f2,axiom,(
% 19.05/3.00    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 19.05/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.00  
% 19.05/3.00  fof(f17,plain,(
% 19.05/3.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 19.05/3.00    inference(cnf_transformation,[],[f2])).
% 19.05/3.00  
% 19.05/3.00  cnf(c_62,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_61,plain,( X0 = X0 ),theory(equality) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_564,plain,
% 19.05/3.00      ( X0 != X1 | X1 = X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_62,c_61]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_66,plain,
% 19.05/3.00      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 19.05/3.00      theory(equality) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_939,plain,
% 19.05/3.00      ( X0 != X1 | k1_tarski(X1) = k1_tarski(X0) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_564,c_66]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_565,plain,
% 19.05/3.00      ( X0 != X1 | X2 != k1_tarski(X1) | k1_tarski(X0) = X2 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_62,c_66]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_6429,plain,
% 19.05/3.00      ( X0 != X1 | X2 != X0 | k1_tarski(X2) = k1_tarski(X1) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_939,c_565]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_7,negated_conjecture,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
% 19.05/3.00      inference(cnf_transformation,[],[f22]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_935,plain,
% 19.05/3.00      ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_564,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_76566,plain,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0
% 19.05/3.00      | k1_tarski(k1_tarski(sK0)) = k1_tarski(X0) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_6429,c_935]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_4,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
% 19.05/3.00      inference(cnf_transformation,[],[f24]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_12,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_4]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_65,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.05/3.00      theory(equality) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_756,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | ~ r1_xboole_0(X1,k1_tarski(sK0))
% 19.05/3.00      | X0 != X1 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_65,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1247,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))
% 19.05/3.00      | r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_756,c_935]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1051,plain,
% 19.05/3.00      ( k3_xboole_0(X0,k1_tarski(sK1)) = k3_xboole_0(X0,k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_61]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1720,plain,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_1051]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_986,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | r1_xboole_0(X1,k1_tarski(sK0))
% 19.05/3.00      | X1 != X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_935,c_65]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_760,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_65,c_61]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_962,plain,
% 19.05/3.00      ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
% 19.05/3.00      | ~ r1_xboole_0(k1_tarski(sK0),X0) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_760,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1897,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k1_tarski(sK0))
% 19.05/3.00      | ~ r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_986,c_962]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_7360,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_1897,c_935]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1782,plain,
% 19.05/3.00      ( r1_xboole_0(X0,X1)
% 19.05/3.00      | ~ r1_xboole_0(X2,k1_tarski(sK0))
% 19.05/3.00      | X0 != X2
% 19.05/3.00      | X1 != k1_tarski(sK0) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_65]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_7176,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | ~ r1_xboole_0(X1,k1_tarski(sK0))
% 19.05/3.00      | X0 != X1
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_1782]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_31776,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,k1_tarski(sK0))
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_7176]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1611,plain,
% 19.05/3.00      ( r1_xboole_0(X0,X1)
% 19.05/3.00      | ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2)
% 19.05/3.00      | X1 != X2
% 19.05/3.00      | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_65]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_4309,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X1)
% 19.05/3.00      | X1 != X0
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_1611]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_10964,plain,
% 19.05/3.00      ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X0)
% 19.05/3.00      | ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(X1)))
% 19.05/3.00      | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(X1))
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_4309]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_41333,plain,
% 19.05/3.00      ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
% 19.05/3.00      | k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_10964]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_0,plain,
% 19.05/3.00      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 19.05/3.00      inference(cnf_transformation,[],[f16]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_927,plain,
% 19.05/3.00      ( X0 = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_564,c_0]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_6382,plain,
% 19.05/3.00      ( X0 = X1 | X1 != k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_927,c_62]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_562,plain,
% 19.05/3.00      ( X0 != k1_tarski(sK0)
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_62,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_59699,plain,
% 19.05/3.00      ( X0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
% 19.05/3.00      | k2_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_tarski(sK0) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_6382,c_562]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_555,plain,
% 19.05/3.00      ( X0 != X1 | k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_62,c_0]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_2096,plain,
% 19.05/3.00      ( X0 != X1 | X2 != X0 | k2_xboole_0(X1,k3_xboole_0(X1,X3)) = X2 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_555,c_62]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_13326,plain,
% 19.05/3.00      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_tarski(sK0)
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_2096,c_935]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_61276,plain,
% 19.05/3.00      ( X0 = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_59699,c_13326]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_6391,plain,
% 19.05/3.00      ( r1_xboole_0(X0,X1)
% 19.05/3.00      | ~ r1_xboole_0(X2,k2_xboole_0(X1,k3_xboole_0(X1,X3)))
% 19.05/3.00      | X0 != X2 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_927,c_65]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_2099,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,X1)
% 19.05/3.00      | r1_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X3,X4)))
% 19.05/3.00      | X2 != X0
% 19.05/3.00      | X1 != X3 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_555,c_65]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_18665,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
% 19.05/3.00      | ~ r1_xboole_0(X2,k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
% 19.05/3.00      | X0 != X2 ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_2099,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_2,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,X1)
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ),
% 19.05/3.00      inference(cnf_transformation,[],[f18]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_19009,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
% 19.05/3.00      | ~ r1_xboole_0(X2,k1_tarski(sK1))
% 19.05/3.00      | X0 != k3_xboole_0(k1_tarski(sK0),X2) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_18665,c_2]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_19378,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,k1_tarski(sK1))
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
% 19.05/3.00      | k3_xboole_0(k1_tarski(sK0),X0) != k1_tarski(sK0) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_19009,c_562]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_6,negated_conjecture,
% 19.05/3.00      ( sK0 != sK1 ),
% 19.05/3.00      inference(cnf_transformation,[],[f23]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_5,plain,
% 19.05/3.00      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 19.05/3.00      inference(cnf_transformation,[],[f21]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_9,plain,
% 19.05/3.00      ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | sK0 = sK0 ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_5]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_197,plain,
% 19.05/3.00      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_62]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_198,plain,
% 19.05/3.00      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_197]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_153,plain,
% 19.05/3.00      ( X0 = X1 | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 19.05/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_3,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,X1)
% 19.05/3.00      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
% 19.05/3.00      inference(cnf_transformation,[],[f19]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_155,plain,
% 19.05/3.00      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
% 19.05/3.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.05/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_922,plain,
% 19.05/3.00      ( X0 = X1
% 19.05/3.00      | k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2) ),
% 19.05/3.00      inference(superposition,[status(thm)],[c_153,c_155]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_1,plain,
% 19.05/3.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.05/3.00      inference(cnf_transformation,[],[f17]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_378,plain,
% 19.05/3.00      ( k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) ),
% 19.05/3.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_383,plain,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k1_tarski(sK0) ),
% 19.05/3.00      inference(demodulation,[status(thm)],[c_378,c_0]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_3502,plain,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),X0) = k1_tarski(sK0) | sK1 = sK0 ),
% 19.05/3.00      inference(superposition,[status(thm)],[c_922,c_383]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_51512,plain,
% 19.05/3.00      ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1)))
% 19.05/3.00      | ~ r1_xboole_0(X0,k1_tarski(sK1)) ),
% 19.05/3.00      inference(global_propositional_subsumption,
% 19.05/3.00                [status(thm)],
% 19.05/3.00                [c_19378,c_6,c_9,c_12,c_198,c_3502]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_51513,plain,
% 19.05/3.00      ( ~ r1_xboole_0(X0,k1_tarski(sK1))
% 19.05/3.00      | r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X1))) ),
% 19.05/3.00      inference(renaming,[status(thm)],[c_51512]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_51534,plain,
% 19.05/3.00      ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0)))
% 19.05/3.00      | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_51513,c_962]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_224,plain,
% 19.05/3.00      ( r1_xboole_0(k1_tarski(X0),k1_tarski(sK1)) | sK1 = X0 ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_5]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_226,plain,
% 19.05/3.00      ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK1 = sK0 ),
% 19.05/3.00      inference(instantiation,[status(thm)],[c_224]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_52272,plain,
% 19.05/3.00      ( r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))) ),
% 19.05/3.00      inference(global_propositional_subsumption,
% 19.05/3.00                [status(thm)],
% 19.05/3.00                [c_51534,c_6,c_9,c_12,c_198,c_226]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_76444,plain,
% 19.05/3.00      ( r1_xboole_0(X0,k1_tarski(sK0))
% 19.05/3.00      | X0 != k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
% 19.05/3.00      inference(resolution,[status(thm)],[c_6391,c_52272]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_78216,plain,
% 19.05/3.00      ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != X0 ),
% 19.05/3.00      inference(global_propositional_subsumption,
% 19.05/3.00                [status(thm)],
% 19.05/3.00                [c_76566,c_7,c_12,c_935,c_1247,c_1720,c_7360,c_31776,c_41333,
% 19.05/3.00                 c_61276,c_76444]) ).
% 19.05/3.00  
% 19.05/3.00  cnf(c_78231,plain,
% 19.05/3.00      ( $false ),
% 19.05/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_78216,c_7]) ).
% 19.05/3.00  
% 19.05/3.00  
% 19.05/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.05/3.00  
% 19.05/3.00  ------                               Statistics
% 19.05/3.00  
% 19.05/3.00  ------ Selected
% 19.05/3.00  
% 19.05/3.00  total_time:                             2.296
% 19.05/3.00  
%------------------------------------------------------------------------------
