%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0883+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:20 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of clauses        :   33 (  39 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 114 expanded)
%              Number of equality atoms :   86 ( 113 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f15,f21,f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).

fof(f22,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    inference(definition_unfolding,[],[f22,f14,f21,f13,f13,f13,f13])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))) ),
    inference(definition_unfolding,[],[f18,f21])).

cnf(c_28,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_520,plain,
    ( X0_38 != X1_38
    | X0_38 = k2_zfmisc_1(X2_38,X3_38)
    | k2_zfmisc_1(X2_38,X3_38) != X1_38 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_946,plain,
    ( X0_38 != k2_zfmisc_1(X1_38,X2_38)
    | X0_38 = k2_zfmisc_1(X3_38,X4_38)
    | k2_zfmisc_1(X3_38,X4_38) != k2_zfmisc_1(X1_38,X2_38) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_1822,plain,
    ( k2_zfmisc_1(X0_38,X1_38) != k2_zfmisc_1(k2_xboole_0(X2_38,X3_38),X4_38)
    | k2_xboole_0(k2_zfmisc_1(X2_38,X4_38),k2_zfmisc_1(X3_38,X4_38)) = k2_zfmisc_1(X0_38,X1_38)
    | k2_xboole_0(k2_zfmisc_1(X2_38,X4_38),k2_zfmisc_1(X3_38,X4_38)) != k2_zfmisc_1(k2_xboole_0(X2_38,X3_38),X4_38) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_14408,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k1_tarski(sK4))
    | k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) = k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4))
    | k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_24,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38)) = k2_zfmisc_1(k2_xboole_0(X0_38,X2_38),X1_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_8567,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) = k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( X0_38 != X1_38
    | X2_38 != X3_38
    | k2_zfmisc_1(X0_38,X2_38) = k2_zfmisc_1(X1_38,X3_38) ),
    theory(equality)).

cnf(c_67,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) = k2_zfmisc_1(X0_38,X1_38)
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != X0_38
    | k1_tarski(sK4) != X1_38 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) = k2_zfmisc_1(X0_38,k1_tarski(sK4))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != X0_38
    | k1_tarski(sK4) != k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2712,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))),k1_tarski(sK4))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)))
    | k1_tarski(sK4) != k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_26,plain,
    ( k2_xboole_0(k2_tarski(X0_39,X1_39),k2_tarski(X2_39,X3_39)) = k2_xboole_0(k2_tarski(X0_39,X2_39),k2_tarski(X1_39,X3_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1211,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))) = k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_123,plain,
    ( X0_38 != X1_38
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != X1_38
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = X0_38 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_691,plain,
    ( X0_38 != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = X0_38
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_1210,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))
    | k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3))) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_4,plain,
    ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_tarski(X0,X2),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_22,plain,
    ( k2_tarski(k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k2_tarski(X0_39,X2_39),k1_tarski(X1_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_6,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_20,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_153,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(superposition,[status(thm)],[c_22,c_20])).

cnf(c_554,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(superposition,[status(thm)],[c_22,c_153])).

cnf(c_194,plain,
    ( X0_38 != k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = X0_38
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_479,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))
    | k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) != k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_27,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_195,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) = k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_23,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)),k2_tarski(k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39))) = k2_zfmisc_1(k2_tarski(X0_39,X3_39),k2_tarski(X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_186,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) = k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_83,plain,
    ( k1_tarski(sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14408,c_8567,c_2712,c_1211,c_1210,c_554,c_479,c_195,c_186,c_83])).


%------------------------------------------------------------------------------
