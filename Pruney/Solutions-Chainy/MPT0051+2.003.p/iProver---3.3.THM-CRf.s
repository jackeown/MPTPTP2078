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
% DateTime   : Thu Dec  3 11:22:41 EST 2020

% Result     : Theorem 39.42s
% Output     : CNFRefutation 39.42s
% Verified   : 
% Statistics : Number of formulae       :  166 (22221 expanded)
%              Number of clauses        :  145 (10194 expanded)
%              Number of leaves         :   11 (4863 expanded)
%              Depth                    :   40
%              Number of atoms          :  221 (32666 expanded)
%              Number of equality atoms :  177 (17878 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_69,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(X0,X1)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_171649,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_171651,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_171649])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_158,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_162,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_696,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_158,c_162])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_161,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1112,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_161])).

cnf(c_1381,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1112])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_777,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_696,c_0])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_493,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_2176,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_696,c_493])).

cnf(c_2203,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_2176,c_2])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_160,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_293,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_160])).

cnf(c_2735,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_293])).

cnf(c_18716,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_161])).

cnf(c_18722,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18716,c_3])).

cnf(c_18723,plain,
    ( r1_tarski(k4_xboole_0(X0,sK2),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18722,c_696])).

cnf(c_18934,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),sK2),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_18723,c_161])).

cnf(c_18942,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK2,X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18934,c_3])).

cnf(c_23498,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_18942])).

cnf(c_24440,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),X0) = X0 ),
    inference(superposition,[status(thm)],[c_23498,c_162])).

cnf(c_31186,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2)) = X0 ),
    inference(superposition,[status(thm)],[c_24440,c_0])).

cnf(c_1382,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2) = sK2
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_162])).

cnf(c_1849,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_158,c_1382])).

cnf(c_1875,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1849,c_3])).

cnf(c_1876,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1875,c_2])).

cnf(c_2345,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_0,c_1876])).

cnf(c_323,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_293])).

cnf(c_427,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_323])).

cnf(c_438,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_427])).

cnf(c_1106,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_438,c_161])).

cnf(c_1119,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1106,c_3])).

cnf(c_1275,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1119])).

cnf(c_1282,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1275,c_2])).

cnf(c_1858,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,sK2)),k4_xboole_0(sK0,sK1)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1282,c_1382])).

cnf(c_1859,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1))),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1858,c_3])).

cnf(c_494,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_3,c_3])).

cnf(c_497,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_494,c_3])).

cnf(c_1860,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1859,c_497])).

cnf(c_1861,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,sK2)),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1860,c_777])).

cnf(c_2132,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X0,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1861,c_0])).

cnf(c_3515,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2345,c_2132])).

cnf(c_3523,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_3515,c_2,c_3,c_493])).

cnf(c_6812,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1))) = k4_xboole_0(X0,k2_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_696,c_497])).

cnf(c_7422,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X0)),k4_xboole_0(X1,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6812,c_2])).

cnf(c_10604,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1)),X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1))),k4_xboole_0(X2,k2_xboole_0(sK2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7422,c_161])).

cnf(c_10623,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1)),X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,X1)),k4_xboole_0(X2,k2_xboole_0(sK2,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10604,c_6812])).

cnf(c_13279,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X1)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),k4_xboole_0(X1,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3523,c_10623])).

cnf(c_13280,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,X1)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13279,c_696,c_3523])).

cnf(c_13731,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK2)) = k4_xboole_0(X1,sK2)
    | r1_tarski(X0,k2_xboole_0(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13280,c_162])).

cnf(c_56807,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2),sK2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2),sK2)
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31186,c_13731])).

cnf(c_15521,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(X0,sK2)) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_160,c_13731])).

cnf(c_26057,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_15521,c_0])).

cnf(c_18933,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),X0) = X0 ),
    inference(superposition,[status(thm)],[c_18723,c_162])).

cnf(c_18973,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,sK2)) = X0 ),
    inference(superposition,[status(thm)],[c_18933,c_0])).

cnf(c_26081,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_15521,c_18973])).

cnf(c_56922,plain,
    ( k4_xboole_0(X0,sK2) = k4_xboole_0(sK2,sK2)
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_56807,c_696,c_26057,c_26081])).

cnf(c_57577,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK0,sK1))),sK2) = k4_xboole_0(sK2,sK2)
    | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_56922])).

cnf(c_57631,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = k4_xboole_0(sK2,sK2)
    | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_57577,c_3,c_497])).

cnf(c_57632,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,sK2)) = k4_xboole_0(sK2,sK2)
    | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57631,c_696])).

cnf(c_57656,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_158,c_57632])).

cnf(c_599,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_438])).

cnf(c_703,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_599,c_162])).

cnf(c_62543,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_703])).

cnf(c_137668,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_57656,c_62543])).

cnf(c_701,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_438,c_162])).

cnf(c_58265,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_57656,c_701])).

cnf(c_1365,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1282,c_162])).

cnf(c_1101,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_160,c_161])).

cnf(c_66080,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_161])).

cnf(c_66098,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_66080,c_3])).

cnf(c_66354,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_66098,c_56922])).

cnf(c_70091,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_66354,c_18973])).

cnf(c_66351,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2) = X2 ),
    inference(superposition,[status(thm)],[c_66098,c_162])).

cnf(c_70114,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_70091,c_66351])).

cnf(c_102372,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1365,c_1365,c_70114])).

cnf(c_58273,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_57656,c_2])).

cnf(c_695,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_160,c_162])).

cnf(c_31922,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_695])).

cnf(c_59057,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_58273,c_31922])).

cnf(c_698,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_323,c_162])).

cnf(c_58278,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_57656,c_698])).

cnf(c_59145,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(light_normalisation,[status(thm)],[c_59057,c_58278])).

cnf(c_102377,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_102372,c_59145])).

cnf(c_138268,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_137668,c_58265,c_102377])).

cnf(c_66081,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1101,c_57632])).

cnf(c_68170,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(X0,sK2),X0)) = k2_xboole_0(k2_xboole_0(X0,sK2),X0) ),
    inference(superposition,[status(thm)],[c_66081,c_701])).

cnf(c_68177,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,sK2),X0) ),
    inference(superposition,[status(thm)],[c_66081,c_2])).

cnf(c_2172,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_493])).

cnf(c_68223,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,sK2)) = k2_xboole_0(X0,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_66081,c_2172])).

cnf(c_68275,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sK2,sK2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_68223,c_18973])).

cnf(c_68304,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),X0) = k2_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_68177,c_68275])).

cnf(c_68311,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_68170,c_68304])).

cnf(c_138269,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_138268,c_68311])).

cnf(c_697,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_293,c_162])).

cnf(c_36661,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_697,c_493])).

cnf(c_36811,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_36661,c_2])).

cnf(c_127912,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),sK0) ),
    inference(superposition,[status(thm)],[c_57656,c_36811])).

cnf(c_1279,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),X0)),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_161])).

cnf(c_1280,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),X0),X1)),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1279,c_3])).

cnf(c_1281,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),k2_xboole_0(X0,X1))),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1280,c_497])).

cnf(c_98906,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X0,k4_xboole_0(sK0,sK1)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_1281])).

cnf(c_100816,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_98906])).

cnf(c_101098,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0)),sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_100816,c_57632])).

cnf(c_117339,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))),k2_xboole_0(X0,k4_xboole_0(sK0,sK1))),sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_697,c_101098])).

cnf(c_36570,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_697])).

cnf(c_36979,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_695,c_36570])).

cnf(c_37249,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_36979,c_36570])).

cnf(c_36975,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_36570])).

cnf(c_37251,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_36975,c_36570])).

cnf(c_66353,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_66098,c_57632])).

cnf(c_69697,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_697,c_66353])).

cnf(c_117551,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_117339,c_497,c_37249,c_37251,c_69697])).

cnf(c_117552,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_117551,c_696])).

cnf(c_118028,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_117552,c_497])).

cnf(c_43101,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_698,c_0])).

cnf(c_121913,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_118028,c_43101])).

cnf(c_121922,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_118028,c_2])).

cnf(c_122103,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) = k2_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
    inference(demodulation,[status(thm)],[c_121922,c_68275])).

cnf(c_122118,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
    inference(demodulation,[status(thm)],[c_121913,c_122103])).

cnf(c_128321,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_127912,c_122118])).

cnf(c_130138,plain,
    ( r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_128321,c_293])).

cnf(c_130257,plain,
    ( r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_130138])).

cnf(c_130259,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_130257])).

cnf(c_67,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_214,plain,
    ( X0 != X1
    | k2_xboole_0(sK1,sK2) != X1
    | k2_xboole_0(sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_256,plain,
    ( X0 != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = X0
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_358,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_359,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_66,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_249,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_74,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_171651,c_138269,c_130259,c_359,c_249,c_74,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.42/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.42/5.48  
% 39.42/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.42/5.48  
% 39.42/5.48  ------  iProver source info
% 39.42/5.48  
% 39.42/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.42/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.42/5.48  git: non_committed_changes: false
% 39.42/5.48  git: last_make_outside_of_git: false
% 39.42/5.48  
% 39.42/5.48  ------ 
% 39.42/5.48  
% 39.42/5.48  ------ Input Options
% 39.42/5.48  
% 39.42/5.48  --out_options                           all
% 39.42/5.48  --tptp_safe_out                         true
% 39.42/5.48  --problem_path                          ""
% 39.42/5.48  --include_path                          ""
% 39.42/5.48  --clausifier                            res/vclausify_rel
% 39.42/5.48  --clausifier_options                    ""
% 39.42/5.48  --stdin                                 false
% 39.42/5.48  --stats_out                             all
% 39.42/5.48  
% 39.42/5.48  ------ General Options
% 39.42/5.48  
% 39.42/5.48  --fof                                   false
% 39.42/5.48  --time_out_real                         305.
% 39.42/5.48  --time_out_virtual                      -1.
% 39.42/5.48  --symbol_type_check                     false
% 39.42/5.48  --clausify_out                          false
% 39.42/5.48  --sig_cnt_out                           false
% 39.42/5.48  --trig_cnt_out                          false
% 39.42/5.48  --trig_cnt_out_tolerance                1.
% 39.42/5.48  --trig_cnt_out_sk_spl                   false
% 39.42/5.48  --abstr_cl_out                          false
% 39.42/5.48  
% 39.42/5.48  ------ Global Options
% 39.42/5.48  
% 39.42/5.48  --schedule                              default
% 39.42/5.48  --add_important_lit                     false
% 39.42/5.48  --prop_solver_per_cl                    1000
% 39.42/5.48  --min_unsat_core                        false
% 39.42/5.48  --soft_assumptions                      false
% 39.42/5.48  --soft_lemma_size                       3
% 39.42/5.48  --prop_impl_unit_size                   0
% 39.42/5.48  --prop_impl_unit                        []
% 39.42/5.48  --share_sel_clauses                     true
% 39.42/5.48  --reset_solvers                         false
% 39.42/5.48  --bc_imp_inh                            [conj_cone]
% 39.42/5.48  --conj_cone_tolerance                   3.
% 39.42/5.48  --extra_neg_conj                        none
% 39.42/5.48  --large_theory_mode                     true
% 39.42/5.48  --prolific_symb_bound                   200
% 39.42/5.48  --lt_threshold                          2000
% 39.42/5.48  --clause_weak_htbl                      true
% 39.42/5.48  --gc_record_bc_elim                     false
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing Options
% 39.42/5.48  
% 39.42/5.48  --preprocessing_flag                    true
% 39.42/5.48  --time_out_prep_mult                    0.1
% 39.42/5.48  --splitting_mode                        input
% 39.42/5.48  --splitting_grd                         true
% 39.42/5.48  --splitting_cvd                         false
% 39.42/5.48  --splitting_cvd_svl                     false
% 39.42/5.48  --splitting_nvd                         32
% 39.42/5.48  --sub_typing                            true
% 39.42/5.48  --prep_gs_sim                           true
% 39.42/5.48  --prep_unflatten                        true
% 39.42/5.48  --prep_res_sim                          true
% 39.42/5.48  --prep_upred                            true
% 39.42/5.48  --prep_sem_filter                       exhaustive
% 39.42/5.48  --prep_sem_filter_out                   false
% 39.42/5.48  --pred_elim                             true
% 39.42/5.48  --res_sim_input                         true
% 39.42/5.48  --eq_ax_congr_red                       true
% 39.42/5.48  --pure_diseq_elim                       true
% 39.42/5.48  --brand_transform                       false
% 39.42/5.48  --non_eq_to_eq                          false
% 39.42/5.48  --prep_def_merge                        true
% 39.42/5.48  --prep_def_merge_prop_impl              false
% 39.42/5.48  --prep_def_merge_mbd                    true
% 39.42/5.48  --prep_def_merge_tr_red                 false
% 39.42/5.48  --prep_def_merge_tr_cl                  false
% 39.42/5.48  --smt_preprocessing                     true
% 39.42/5.48  --smt_ac_axioms                         fast
% 39.42/5.48  --preprocessed_out                      false
% 39.42/5.48  --preprocessed_stats                    false
% 39.42/5.48  
% 39.42/5.48  ------ Abstraction refinement Options
% 39.42/5.48  
% 39.42/5.48  --abstr_ref                             []
% 39.42/5.48  --abstr_ref_prep                        false
% 39.42/5.48  --abstr_ref_until_sat                   false
% 39.42/5.48  --abstr_ref_sig_restrict                funpre
% 39.42/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.42/5.48  --abstr_ref_under                       []
% 39.42/5.48  
% 39.42/5.48  ------ SAT Options
% 39.42/5.48  
% 39.42/5.48  --sat_mode                              false
% 39.42/5.48  --sat_fm_restart_options                ""
% 39.42/5.48  --sat_gr_def                            false
% 39.42/5.48  --sat_epr_types                         true
% 39.42/5.48  --sat_non_cyclic_types                  false
% 39.42/5.48  --sat_finite_models                     false
% 39.42/5.48  --sat_fm_lemmas                         false
% 39.42/5.48  --sat_fm_prep                           false
% 39.42/5.48  --sat_fm_uc_incr                        true
% 39.42/5.48  --sat_out_model                         small
% 39.42/5.48  --sat_out_clauses                       false
% 39.42/5.48  
% 39.42/5.48  ------ QBF Options
% 39.42/5.48  
% 39.42/5.48  --qbf_mode                              false
% 39.42/5.48  --qbf_elim_univ                         false
% 39.42/5.48  --qbf_dom_inst                          none
% 39.42/5.48  --qbf_dom_pre_inst                      false
% 39.42/5.48  --qbf_sk_in                             false
% 39.42/5.48  --qbf_pred_elim                         true
% 39.42/5.48  --qbf_split                             512
% 39.42/5.48  
% 39.42/5.48  ------ BMC1 Options
% 39.42/5.48  
% 39.42/5.48  --bmc1_incremental                      false
% 39.42/5.48  --bmc1_axioms                           reachable_all
% 39.42/5.48  --bmc1_min_bound                        0
% 39.42/5.48  --bmc1_max_bound                        -1
% 39.42/5.48  --bmc1_max_bound_default                -1
% 39.42/5.48  --bmc1_symbol_reachability              true
% 39.42/5.48  --bmc1_property_lemmas                  false
% 39.42/5.48  --bmc1_k_induction                      false
% 39.42/5.48  --bmc1_non_equiv_states                 false
% 39.42/5.48  --bmc1_deadlock                         false
% 39.42/5.48  --bmc1_ucm                              false
% 39.42/5.48  --bmc1_add_unsat_core                   none
% 39.42/5.48  --bmc1_unsat_core_children              false
% 39.42/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.42/5.48  --bmc1_out_stat                         full
% 39.42/5.48  --bmc1_ground_init                      false
% 39.42/5.48  --bmc1_pre_inst_next_state              false
% 39.42/5.48  --bmc1_pre_inst_state                   false
% 39.42/5.48  --bmc1_pre_inst_reach_state             false
% 39.42/5.48  --bmc1_out_unsat_core                   false
% 39.42/5.48  --bmc1_aig_witness_out                  false
% 39.42/5.48  --bmc1_verbose                          false
% 39.42/5.48  --bmc1_dump_clauses_tptp                false
% 39.42/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.42/5.48  --bmc1_dump_file                        -
% 39.42/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.42/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.42/5.48  --bmc1_ucm_extend_mode                  1
% 39.42/5.48  --bmc1_ucm_init_mode                    2
% 39.42/5.48  --bmc1_ucm_cone_mode                    none
% 39.42/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.42/5.48  --bmc1_ucm_relax_model                  4
% 39.42/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.42/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.42/5.48  --bmc1_ucm_layered_model                none
% 39.42/5.48  --bmc1_ucm_max_lemma_size               10
% 39.42/5.48  
% 39.42/5.48  ------ AIG Options
% 39.42/5.48  
% 39.42/5.48  --aig_mode                              false
% 39.42/5.48  
% 39.42/5.48  ------ Instantiation Options
% 39.42/5.48  
% 39.42/5.48  --instantiation_flag                    true
% 39.42/5.48  --inst_sos_flag                         true
% 39.42/5.48  --inst_sos_phase                        true
% 39.42/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.42/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.42/5.48  --inst_lit_sel_side                     num_symb
% 39.42/5.48  --inst_solver_per_active                1400
% 39.42/5.48  --inst_solver_calls_frac                1.
% 39.42/5.48  --inst_passive_queue_type               priority_queues
% 39.42/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.42/5.48  --inst_passive_queues_freq              [25;2]
% 39.42/5.48  --inst_dismatching                      true
% 39.42/5.48  --inst_eager_unprocessed_to_passive     true
% 39.42/5.48  --inst_prop_sim_given                   true
% 39.42/5.48  --inst_prop_sim_new                     false
% 39.42/5.48  --inst_subs_new                         false
% 39.42/5.48  --inst_eq_res_simp                      false
% 39.42/5.48  --inst_subs_given                       false
% 39.42/5.48  --inst_orphan_elimination               true
% 39.42/5.48  --inst_learning_loop_flag               true
% 39.42/5.48  --inst_learning_start                   3000
% 39.42/5.48  --inst_learning_factor                  2
% 39.42/5.48  --inst_start_prop_sim_after_learn       3
% 39.42/5.48  --inst_sel_renew                        solver
% 39.42/5.48  --inst_lit_activity_flag                true
% 39.42/5.48  --inst_restr_to_given                   false
% 39.42/5.48  --inst_activity_threshold               500
% 39.42/5.48  --inst_out_proof                        true
% 39.42/5.48  
% 39.42/5.48  ------ Resolution Options
% 39.42/5.48  
% 39.42/5.48  --resolution_flag                       true
% 39.42/5.48  --res_lit_sel                           adaptive
% 39.42/5.48  --res_lit_sel_side                      none
% 39.42/5.48  --res_ordering                          kbo
% 39.42/5.48  --res_to_prop_solver                    active
% 39.42/5.48  --res_prop_simpl_new                    false
% 39.42/5.48  --res_prop_simpl_given                  true
% 39.42/5.48  --res_passive_queue_type                priority_queues
% 39.42/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.42/5.48  --res_passive_queues_freq               [15;5]
% 39.42/5.48  --res_forward_subs                      full
% 39.42/5.48  --res_backward_subs                     full
% 39.42/5.48  --res_forward_subs_resolution           true
% 39.42/5.48  --res_backward_subs_resolution          true
% 39.42/5.48  --res_orphan_elimination                true
% 39.42/5.48  --res_time_limit                        2.
% 39.42/5.48  --res_out_proof                         true
% 39.42/5.48  
% 39.42/5.48  ------ Superposition Options
% 39.42/5.48  
% 39.42/5.48  --superposition_flag                    true
% 39.42/5.48  --sup_passive_queue_type                priority_queues
% 39.42/5.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.42/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.42/5.48  --demod_completeness_check              fast
% 39.42/5.48  --demod_use_ground                      true
% 39.42/5.48  --sup_to_prop_solver                    passive
% 39.42/5.48  --sup_prop_simpl_new                    true
% 39.42/5.48  --sup_prop_simpl_given                  true
% 39.42/5.48  --sup_fun_splitting                     true
% 39.42/5.48  --sup_smt_interval                      50000
% 39.42/5.48  
% 39.42/5.48  ------ Superposition Simplification Setup
% 39.42/5.48  
% 39.42/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.42/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.42/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.42/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.42/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.42/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.42/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.42/5.48  --sup_immed_triv                        [TrivRules]
% 39.42/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_immed_bw_main                     []
% 39.42/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.42/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.42/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_input_bw                          []
% 39.42/5.48  
% 39.42/5.48  ------ Combination Options
% 39.42/5.48  
% 39.42/5.48  --comb_res_mult                         3
% 39.42/5.48  --comb_sup_mult                         2
% 39.42/5.48  --comb_inst_mult                        10
% 39.42/5.48  
% 39.42/5.48  ------ Debug Options
% 39.42/5.48  
% 39.42/5.48  --dbg_backtrace                         false
% 39.42/5.48  --dbg_dump_prop_clauses                 false
% 39.42/5.48  --dbg_dump_prop_clauses_file            -
% 39.42/5.48  --dbg_out_stat                          false
% 39.42/5.48  ------ Parsing...
% 39.42/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.42/5.48  ------ Proving...
% 39.42/5.48  ------ Problem Properties 
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  clauses                                 8
% 39.42/5.48  conjectures                             2
% 39.42/5.48  EPR                                     0
% 39.42/5.48  Horn                                    8
% 39.42/5.48  unary                                   6
% 39.42/5.48  binary                                  2
% 39.42/5.48  lits                                    10
% 39.42/5.48  lits eq                                 4
% 39.42/5.48  fd_pure                                 0
% 39.42/5.48  fd_pseudo                               0
% 39.42/5.48  fd_cond                                 0
% 39.42/5.48  fd_pseudo_cond                          0
% 39.42/5.48  AC symbols                              0
% 39.42/5.48  
% 39.42/5.48  ------ Schedule dynamic 5 is on 
% 39.42/5.48  
% 39.42/5.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  ------ 
% 39.42/5.48  Current options:
% 39.42/5.48  ------ 
% 39.42/5.48  
% 39.42/5.48  ------ Input Options
% 39.42/5.48  
% 39.42/5.48  --out_options                           all
% 39.42/5.48  --tptp_safe_out                         true
% 39.42/5.48  --problem_path                          ""
% 39.42/5.48  --include_path                          ""
% 39.42/5.48  --clausifier                            res/vclausify_rel
% 39.42/5.48  --clausifier_options                    ""
% 39.42/5.48  --stdin                                 false
% 39.42/5.48  --stats_out                             all
% 39.42/5.48  
% 39.42/5.48  ------ General Options
% 39.42/5.48  
% 39.42/5.48  --fof                                   false
% 39.42/5.48  --time_out_real                         305.
% 39.42/5.48  --time_out_virtual                      -1.
% 39.42/5.48  --symbol_type_check                     false
% 39.42/5.48  --clausify_out                          false
% 39.42/5.48  --sig_cnt_out                           false
% 39.42/5.48  --trig_cnt_out                          false
% 39.42/5.48  --trig_cnt_out_tolerance                1.
% 39.42/5.48  --trig_cnt_out_sk_spl                   false
% 39.42/5.48  --abstr_cl_out                          false
% 39.42/5.48  
% 39.42/5.48  ------ Global Options
% 39.42/5.48  
% 39.42/5.48  --schedule                              default
% 39.42/5.48  --add_important_lit                     false
% 39.42/5.48  --prop_solver_per_cl                    1000
% 39.42/5.48  --min_unsat_core                        false
% 39.42/5.48  --soft_assumptions                      false
% 39.42/5.48  --soft_lemma_size                       3
% 39.42/5.48  --prop_impl_unit_size                   0
% 39.42/5.48  --prop_impl_unit                        []
% 39.42/5.48  --share_sel_clauses                     true
% 39.42/5.48  --reset_solvers                         false
% 39.42/5.48  --bc_imp_inh                            [conj_cone]
% 39.42/5.48  --conj_cone_tolerance                   3.
% 39.42/5.48  --extra_neg_conj                        none
% 39.42/5.48  --large_theory_mode                     true
% 39.42/5.48  --prolific_symb_bound                   200
% 39.42/5.48  --lt_threshold                          2000
% 39.42/5.48  --clause_weak_htbl                      true
% 39.42/5.48  --gc_record_bc_elim                     false
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing Options
% 39.42/5.48  
% 39.42/5.48  --preprocessing_flag                    true
% 39.42/5.48  --time_out_prep_mult                    0.1
% 39.42/5.48  --splitting_mode                        input
% 39.42/5.48  --splitting_grd                         true
% 39.42/5.48  --splitting_cvd                         false
% 39.42/5.48  --splitting_cvd_svl                     false
% 39.42/5.48  --splitting_nvd                         32
% 39.42/5.48  --sub_typing                            true
% 39.42/5.48  --prep_gs_sim                           true
% 39.42/5.48  --prep_unflatten                        true
% 39.42/5.48  --prep_res_sim                          true
% 39.42/5.48  --prep_upred                            true
% 39.42/5.48  --prep_sem_filter                       exhaustive
% 39.42/5.48  --prep_sem_filter_out                   false
% 39.42/5.48  --pred_elim                             true
% 39.42/5.48  --res_sim_input                         true
% 39.42/5.48  --eq_ax_congr_red                       true
% 39.42/5.48  --pure_diseq_elim                       true
% 39.42/5.48  --brand_transform                       false
% 39.42/5.48  --non_eq_to_eq                          false
% 39.42/5.48  --prep_def_merge                        true
% 39.42/5.48  --prep_def_merge_prop_impl              false
% 39.42/5.48  --prep_def_merge_mbd                    true
% 39.42/5.48  --prep_def_merge_tr_red                 false
% 39.42/5.48  --prep_def_merge_tr_cl                  false
% 39.42/5.48  --smt_preprocessing                     true
% 39.42/5.48  --smt_ac_axioms                         fast
% 39.42/5.48  --preprocessed_out                      false
% 39.42/5.48  --preprocessed_stats                    false
% 39.42/5.48  
% 39.42/5.48  ------ Abstraction refinement Options
% 39.42/5.48  
% 39.42/5.48  --abstr_ref                             []
% 39.42/5.48  --abstr_ref_prep                        false
% 39.42/5.48  --abstr_ref_until_sat                   false
% 39.42/5.48  --abstr_ref_sig_restrict                funpre
% 39.42/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.42/5.48  --abstr_ref_under                       []
% 39.42/5.48  
% 39.42/5.48  ------ SAT Options
% 39.42/5.48  
% 39.42/5.48  --sat_mode                              false
% 39.42/5.48  --sat_fm_restart_options                ""
% 39.42/5.48  --sat_gr_def                            false
% 39.42/5.48  --sat_epr_types                         true
% 39.42/5.48  --sat_non_cyclic_types                  false
% 39.42/5.48  --sat_finite_models                     false
% 39.42/5.48  --sat_fm_lemmas                         false
% 39.42/5.48  --sat_fm_prep                           false
% 39.42/5.48  --sat_fm_uc_incr                        true
% 39.42/5.48  --sat_out_model                         small
% 39.42/5.48  --sat_out_clauses                       false
% 39.42/5.48  
% 39.42/5.48  ------ QBF Options
% 39.42/5.48  
% 39.42/5.48  --qbf_mode                              false
% 39.42/5.48  --qbf_elim_univ                         false
% 39.42/5.48  --qbf_dom_inst                          none
% 39.42/5.48  --qbf_dom_pre_inst                      false
% 39.42/5.48  --qbf_sk_in                             false
% 39.42/5.48  --qbf_pred_elim                         true
% 39.42/5.48  --qbf_split                             512
% 39.42/5.48  
% 39.42/5.48  ------ BMC1 Options
% 39.42/5.48  
% 39.42/5.48  --bmc1_incremental                      false
% 39.42/5.48  --bmc1_axioms                           reachable_all
% 39.42/5.48  --bmc1_min_bound                        0
% 39.42/5.48  --bmc1_max_bound                        -1
% 39.42/5.48  --bmc1_max_bound_default                -1
% 39.42/5.48  --bmc1_symbol_reachability              true
% 39.42/5.48  --bmc1_property_lemmas                  false
% 39.42/5.48  --bmc1_k_induction                      false
% 39.42/5.48  --bmc1_non_equiv_states                 false
% 39.42/5.48  --bmc1_deadlock                         false
% 39.42/5.48  --bmc1_ucm                              false
% 39.42/5.48  --bmc1_add_unsat_core                   none
% 39.42/5.48  --bmc1_unsat_core_children              false
% 39.42/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.42/5.48  --bmc1_out_stat                         full
% 39.42/5.48  --bmc1_ground_init                      false
% 39.42/5.48  --bmc1_pre_inst_next_state              false
% 39.42/5.48  --bmc1_pre_inst_state                   false
% 39.42/5.48  --bmc1_pre_inst_reach_state             false
% 39.42/5.48  --bmc1_out_unsat_core                   false
% 39.42/5.48  --bmc1_aig_witness_out                  false
% 39.42/5.48  --bmc1_verbose                          false
% 39.42/5.48  --bmc1_dump_clauses_tptp                false
% 39.42/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.42/5.48  --bmc1_dump_file                        -
% 39.42/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.42/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.42/5.48  --bmc1_ucm_extend_mode                  1
% 39.42/5.48  --bmc1_ucm_init_mode                    2
% 39.42/5.48  --bmc1_ucm_cone_mode                    none
% 39.42/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.42/5.48  --bmc1_ucm_relax_model                  4
% 39.42/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.42/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.42/5.48  --bmc1_ucm_layered_model                none
% 39.42/5.48  --bmc1_ucm_max_lemma_size               10
% 39.42/5.48  
% 39.42/5.48  ------ AIG Options
% 39.42/5.48  
% 39.42/5.48  --aig_mode                              false
% 39.42/5.48  
% 39.42/5.48  ------ Instantiation Options
% 39.42/5.48  
% 39.42/5.48  --instantiation_flag                    true
% 39.42/5.48  --inst_sos_flag                         true
% 39.42/5.48  --inst_sos_phase                        true
% 39.42/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.42/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.42/5.48  --inst_lit_sel_side                     none
% 39.42/5.48  --inst_solver_per_active                1400
% 39.42/5.48  --inst_solver_calls_frac                1.
% 39.42/5.48  --inst_passive_queue_type               priority_queues
% 39.42/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.42/5.48  --inst_passive_queues_freq              [25;2]
% 39.42/5.48  --inst_dismatching                      true
% 39.42/5.48  --inst_eager_unprocessed_to_passive     true
% 39.42/5.48  --inst_prop_sim_given                   true
% 39.42/5.48  --inst_prop_sim_new                     false
% 39.42/5.48  --inst_subs_new                         false
% 39.42/5.48  --inst_eq_res_simp                      false
% 39.42/5.48  --inst_subs_given                       false
% 39.42/5.48  --inst_orphan_elimination               true
% 39.42/5.48  --inst_learning_loop_flag               true
% 39.42/5.48  --inst_learning_start                   3000
% 39.42/5.48  --inst_learning_factor                  2
% 39.42/5.48  --inst_start_prop_sim_after_learn       3
% 39.42/5.48  --inst_sel_renew                        solver
% 39.42/5.48  --inst_lit_activity_flag                true
% 39.42/5.48  --inst_restr_to_given                   false
% 39.42/5.48  --inst_activity_threshold               500
% 39.42/5.48  --inst_out_proof                        true
% 39.42/5.48  
% 39.42/5.48  ------ Resolution Options
% 39.42/5.48  
% 39.42/5.48  --resolution_flag                       false
% 39.42/5.48  --res_lit_sel                           adaptive
% 39.42/5.48  --res_lit_sel_side                      none
% 39.42/5.48  --res_ordering                          kbo
% 39.42/5.48  --res_to_prop_solver                    active
% 39.42/5.48  --res_prop_simpl_new                    false
% 39.42/5.48  --res_prop_simpl_given                  true
% 39.42/5.48  --res_passive_queue_type                priority_queues
% 39.42/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.42/5.48  --res_passive_queues_freq               [15;5]
% 39.42/5.48  --res_forward_subs                      full
% 39.42/5.48  --res_backward_subs                     full
% 39.42/5.48  --res_forward_subs_resolution           true
% 39.42/5.48  --res_backward_subs_resolution          true
% 39.42/5.48  --res_orphan_elimination                true
% 39.42/5.48  --res_time_limit                        2.
% 39.42/5.48  --res_out_proof                         true
% 39.42/5.48  
% 39.42/5.48  ------ Superposition Options
% 39.42/5.48  
% 39.42/5.48  --superposition_flag                    true
% 39.42/5.48  --sup_passive_queue_type                priority_queues
% 39.42/5.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.42/5.48  --sup_passive_queues_freq               [8;1;4]
% 39.42/5.48  --demod_completeness_check              fast
% 39.42/5.48  --demod_use_ground                      true
% 39.42/5.48  --sup_to_prop_solver                    passive
% 39.42/5.48  --sup_prop_simpl_new                    true
% 39.42/5.48  --sup_prop_simpl_given                  true
% 39.42/5.48  --sup_fun_splitting                     true
% 39.42/5.48  --sup_smt_interval                      50000
% 39.42/5.48  
% 39.42/5.48  ------ Superposition Simplification Setup
% 39.42/5.48  
% 39.42/5.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.42/5.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.42/5.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.42/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.42/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.42/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.42/5.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.42/5.48  --sup_immed_triv                        [TrivRules]
% 39.42/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_immed_bw_main                     []
% 39.42/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.42/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.42/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.42/5.48  --sup_input_bw                          []
% 39.42/5.48  
% 39.42/5.48  ------ Combination Options
% 39.42/5.48  
% 39.42/5.48  --comb_res_mult                         3
% 39.42/5.48  --comb_sup_mult                         2
% 39.42/5.48  --comb_inst_mult                        10
% 39.42/5.48  
% 39.42/5.48  ------ Debug Options
% 39.42/5.48  
% 39.42/5.48  --dbg_backtrace                         false
% 39.42/5.48  --dbg_dump_prop_clauses                 false
% 39.42/5.48  --dbg_dump_prop_clauses_file            -
% 39.42/5.48  --dbg_out_stat                          false
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  ------ Proving...
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  % SZS status Theorem for theBenchmark.p
% 39.42/5.48  
% 39.42/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.42/5.48  
% 39.42/5.48  fof(f7,conjecture,(
% 39.42/5.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f8,negated_conjecture,(
% 39.42/5.48    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.42/5.48    inference(negated_conjecture,[],[f7])).
% 39.42/5.48  
% 39.42/5.48  fof(f11,plain,(
% 39.42/5.48    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 39.42/5.48    inference(ennf_transformation,[],[f8])).
% 39.42/5.48  
% 39.42/5.48  fof(f12,plain,(
% 39.42/5.48    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 39.42/5.48    introduced(choice_axiom,[])).
% 39.42/5.48  
% 39.42/5.48  fof(f13,plain,(
% 39.42/5.48    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 39.42/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 39.42/5.48  
% 39.42/5.48  fof(f20,plain,(
% 39.42/5.48    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 39.42/5.48    inference(cnf_transformation,[],[f13])).
% 39.42/5.48  
% 39.42/5.48  fof(f4,axiom,(
% 39.42/5.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f17,plain,(
% 39.42/5.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 39.42/5.48    inference(cnf_transformation,[],[f4])).
% 39.42/5.48  
% 39.42/5.48  fof(f2,axiom,(
% 39.42/5.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f9,plain,(
% 39.42/5.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.42/5.48    inference(ennf_transformation,[],[f2])).
% 39.42/5.48  
% 39.42/5.48  fof(f15,plain,(
% 39.42/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.42/5.48    inference(cnf_transformation,[],[f9])).
% 39.42/5.48  
% 39.42/5.48  fof(f5,axiom,(
% 39.42/5.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f10,plain,(
% 39.42/5.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 39.42/5.48    inference(ennf_transformation,[],[f5])).
% 39.42/5.48  
% 39.42/5.48  fof(f18,plain,(
% 39.42/5.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 39.42/5.48    inference(cnf_transformation,[],[f10])).
% 39.42/5.48  
% 39.42/5.48  fof(f1,axiom,(
% 39.42/5.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f14,plain,(
% 39.42/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.42/5.48    inference(cnf_transformation,[],[f1])).
% 39.42/5.48  
% 39.42/5.48  fof(f3,axiom,(
% 39.42/5.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f16,plain,(
% 39.42/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.42/5.48    inference(cnf_transformation,[],[f3])).
% 39.42/5.48  
% 39.42/5.48  fof(f6,axiom,(
% 39.42/5.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.42/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.42/5.48  
% 39.42/5.48  fof(f19,plain,(
% 39.42/5.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.42/5.48    inference(cnf_transformation,[],[f6])).
% 39.42/5.48  
% 39.42/5.48  fof(f21,plain,(
% 39.42/5.48    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 39.42/5.48    inference(cnf_transformation,[],[f13])).
% 39.42/5.48  
% 39.42/5.48  cnf(c_69,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.42/5.48      theory(equality) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_170,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,X1)
% 39.42/5.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != X1
% 39.42/5.48      | sK0 != X0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_69]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_183,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
% 39.42/5.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != k2_xboole_0(X0,X1)
% 39.42/5.48      | sK0 != X0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_170]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_171649,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))
% 39.42/5.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != k2_xboole_0(X0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | sK0 != X0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_183]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_171651,plain,
% 39.42/5.48      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | ~ r1_tarski(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | sK0 != sK0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_171649]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_7,negated_conjecture,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 39.42/5.48      inference(cnf_transformation,[],[f20]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_158,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 39.42/5.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_3,plain,
% 39.42/5.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 39.42/5.48      inference(cnf_transformation,[],[f17]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.42/5.48      inference(cnf_transformation,[],[f15]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_162,plain,
% 39.42/5.48      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.42/5.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_696,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_158,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_4,plain,
% 39.42/5.48      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 39.42/5.48      inference(cnf_transformation,[],[f18]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_161,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 39.42/5.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1112,plain,
% 39.42/5.48      ( r1_tarski(X0,sK2) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_696,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1381,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK0,sK1))),sK2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_3,c_1112]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_0,plain,
% 39.42/5.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(cnf_transformation,[],[f14]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_777,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_696,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(cnf_transformation,[],[f16]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_493,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2176,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_696,c_493]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2203,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK2,X0) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_2176,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_5,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 39.42/5.48      inference(cnf_transformation,[],[f19]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_160,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.42/5.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_293,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_160]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2735,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK2,X0)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2203,c_293]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18716,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2),X0) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2735,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18722,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),X0) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_18716,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18723,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,sK2),X0) = iProver_top ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_18722,c_696]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18934,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),sK2),X0),X1) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_18723,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18942,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK2,X0)),X1) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_18934,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_23498,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),X0) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_777,c_18942]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_24440,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),X0) = X0 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_23498,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_31186,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2)) = X0 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_24440,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1382,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),sK2) = sK2
% 39.42/5.48      | r1_tarski(X0,sK2) != iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1112,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1849,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_158,c_1382]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1875,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),sK2) = sK2 ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1849,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1876,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2) = sK2 ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1875,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2345,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK2) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_1876]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_323,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2,c_293]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_427,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_323]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_438,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2,c_427]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1106,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),X0),X1) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_438,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1119,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X0)),X1) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1106,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1275,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X1,X0))),X1) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_1119]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1282,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_1275,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1858,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,sK2)),k4_xboole_0(sK0,sK1)),sK2) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1282,c_1382]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1859,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1))),sK2) = sK2 ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1858,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_494,plain,
% 39.42/5.48      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_3,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_497,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_494,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1860,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),sK2) = sK2 ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1859,c_497]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1861,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,sK2)),sK2) = sK2 ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_1860,c_777]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2132,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X0,sK2))) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1861,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_3515,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK2)) = sK2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2345,c_2132]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_3523,plain,
% 39.42/5.48      ( k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) = sK2 ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_3515,c_2,c_3,c_493]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_6812,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1))) = k4_xboole_0(X0,k2_xboole_0(sK2,X1)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_696,c_497]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_7422,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X0)),k4_xboole_0(X1,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X0)),X1) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_6812,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_10604,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1)),X2)) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1))),k4_xboole_0(X2,k2_xboole_0(sK2,X1))) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_7422,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_10623,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X1)),X2)) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,X1)),k4_xboole_0(X2,k2_xboole_0(sK2,X1))) = iProver_top ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_10604,c_6812]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_13279,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),X1)) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),k4_xboole_0(X1,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))))) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_3523,c_10623]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_13280,plain,
% 39.42/5.48      ( r1_tarski(X0,k2_xboole_0(sK2,X1)) != iProver_top
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK2)) = iProver_top ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_13279,c_696,c_3523]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_13731,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK2)) = k4_xboole_0(X1,sK2)
% 39.42/5.48      | r1_tarski(X0,k2_xboole_0(sK2,X1)) != iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_13280,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_56807,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2),sK2)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK2),sK2)
% 39.42/5.48      | r1_tarski(X0,sK2) != iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_31186,c_13731]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_15521,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(X0,sK2)) = k4_xboole_0(X0,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_160,c_13731]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_26057,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) = k4_xboole_0(X0,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_15521,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18933,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,sK2),X0) = X0 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_18723,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_18973,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(X0,sK2)) = X0 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_18933,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_26081,plain,
% 39.42/5.48      ( k4_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_15521,c_18973]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_56922,plain,
% 39.42/5.48      ( k4_xboole_0(X0,sK2) = k4_xboole_0(sK2,sK2)
% 39.42/5.48      | r1_tarski(X0,sK2) != iProver_top ),
% 39.42/5.48      inference(light_normalisation,
% 39.42/5.48                [status(thm)],
% 39.42/5.48                [c_56807,c_696,c_26057,c_26081]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_57577,plain,
% 39.42/5.48      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK0,sK1))),sK2) = k4_xboole_0(sK2,sK2)
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1381,c_56922]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_57631,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = k4_xboole_0(sK2,sK2)
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_57577,c_3,c_497]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_57632,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(X1,sK2)) = k4_xboole_0(sK2,sK2)
% 39.42/5.48      | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_57631,c_696]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_57656,plain,
% 39.42/5.48      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_158,c_57632]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_599,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_438]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_703,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_599,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_62543,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_703]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_137668,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_57656,c_62543]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_701,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_438,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_58265,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_57656,c_701]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1365,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X1) = X1 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1282,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1101,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_160,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66080,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X0),X1),X2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1101,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66098,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_66080,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66354,plain,
% 39.42/5.48      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),sK2) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66098,c_56922]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_70091,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66354,c_18973]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66351,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2) = X2 ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66098,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_70114,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_70091,c_66351]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_102372,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),X0) = X0 ),
% 39.42/5.48      inference(light_normalisation,
% 39.42/5.48                [status(thm)],
% 39.42/5.48                [c_1365,c_1365,c_70114]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_58273,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_57656,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_695,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_160,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_31922,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_695]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_59057,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_58273,c_31922]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_698,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_323,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_58278,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_57656,c_698]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_59145,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_59057,c_58278]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_102377,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_102372,c_59145]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_138268,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 39.42/5.48      inference(light_normalisation,
% 39.42/5.48                [status(thm)],
% 39.42/5.48                [c_137668,c_58265,c_102377]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66081,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1101,c_57632]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68170,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(k2_xboole_0(X0,sK2),X0)) = k2_xboole_0(k2_xboole_0(X0,sK2),X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66081,c_701]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68177,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,sK2),X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66081,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_2172,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_493]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68223,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(X0,sK2)) = k2_xboole_0(X0,k4_xboole_0(sK2,sK2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66081,c_2172]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68275,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k4_xboole_0(sK2,sK2)) = X0 ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_68223,c_18973]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68304,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,sK2),X0) = k2_xboole_0(X0,sK2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_68177,c_68275]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_68311,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)),k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,sK2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_68170,c_68304]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_138269,plain,
% 39.42/5.48      ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_138268,c_68311]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_697,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_293,c_162]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_36661,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_697,c_493]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_36811,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_36661,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_127912,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),sK0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_57656,c_36811]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1279,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),X0)),X1),X2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_1119,c_161]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1280,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),X0),X1)),X2) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1279,c_3]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_1281,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(X1,X2),X0),k2_xboole_0(X0,X1))),X2) = iProver_top ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_1280,c_497]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_98906,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(X0,k4_xboole_0(sK0,sK1)))),sK2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_696,c_1281]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_100816,plain,
% 39.42/5.48      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))),sK2) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_98906]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_101098,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k2_xboole_0(k4_xboole_0(sK0,sK1),X0)),sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_100816,c_57632]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_117339,plain,
% 39.42/5.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))),k2_xboole_0(X0,k4_xboole_0(sK0,sK1))),sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_697,c_101098]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_36570,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_0,c_697]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_36979,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_695,c_36570]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_37249,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_36979,c_36570]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_36975,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_2,c_36570]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_37251,plain,
% 39.42/5.48      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_36975,c_36570]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66353,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_66098,c_57632]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_69697,plain,
% 39.42/5.48      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_697,c_66353]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_117551,plain,
% 39.42/5.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(demodulation,
% 39.42/5.48                [status(thm)],
% 39.42/5.48                [c_117339,c_497,c_37249,c_37251,c_69697]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_117552,plain,
% 39.42/5.48      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,sK2)) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(light_normalisation,[status(thm)],[c_117551,c_696]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_118028,plain,
% 39.42/5.48      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1)),k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = k4_xboole_0(sK2,sK2) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_117552,c_497]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_43101,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_698,c_0]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_121913,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_118028,c_43101]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_121922,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(sK2,sK2)) ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_118028,c_2]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_122103,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(sK0,sK1))) = k2_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_121922,c_68275]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_122118,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_121913,c_122103]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_128321,plain,
% 39.42/5.48      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 39.42/5.48      inference(demodulation,[status(thm)],[c_127912,c_122118]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_130138,plain,
% 39.42/5.48      ( r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 39.42/5.48      inference(superposition,[status(thm)],[c_128321,c_293]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_130257,plain,
% 39.42/5.48      ( r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 39.42/5.48      inference(predicate_to_equality_rev,[status(thm)],[c_130138]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_130259,plain,
% 39.42/5.48      ( r1_tarski(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_130257]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_67,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_214,plain,
% 39.42/5.48      ( X0 != X1
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != X1
% 39.42/5.48      | k2_xboole_0(sK1,sK2) = X0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_67]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_256,plain,
% 39.42/5.48      ( X0 != k2_xboole_0(sK1,sK2)
% 39.42/5.48      | k2_xboole_0(sK1,sK2) = X0
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_214]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_358,plain,
% 39.42/5.48      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK1,sK2)
% 39.42/5.48      | k2_xboole_0(sK1,sK2) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_256]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_359,plain,
% 39.42/5.48      ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
% 39.42/5.48      | k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 39.42/5.48      | k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_358]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_66,plain,( X0 = X0 ),theory(equality) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_249,plain,
% 39.42/5.48      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_66]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_74,plain,
% 39.42/5.48      ( sK0 = sK0 ),
% 39.42/5.48      inference(instantiation,[status(thm)],[c_66]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(c_6,negated_conjecture,
% 39.42/5.48      ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 39.42/5.48      inference(cnf_transformation,[],[f21]) ).
% 39.42/5.48  
% 39.42/5.48  cnf(contradiction,plain,
% 39.42/5.48      ( $false ),
% 39.42/5.48      inference(minisat,
% 39.42/5.48                [status(thm)],
% 39.42/5.48                [c_171651,c_138269,c_130259,c_359,c_249,c_74,c_6]) ).
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.42/5.48  
% 39.42/5.48  ------                               Statistics
% 39.42/5.48  
% 39.42/5.48  ------ General
% 39.42/5.48  
% 39.42/5.48  abstr_ref_over_cycles:                  0
% 39.42/5.48  abstr_ref_under_cycles:                 0
% 39.42/5.48  gc_basic_clause_elim:                   0
% 39.42/5.48  forced_gc_time:                         0
% 39.42/5.48  parsing_time:                           0.007
% 39.42/5.48  unif_index_cands_time:                  0.
% 39.42/5.48  unif_index_add_time:                    0.
% 39.42/5.48  orderings_time:                         0.
% 39.42/5.48  out_proof_time:                         0.016
% 39.42/5.48  total_time:                             4.676
% 39.42/5.48  num_of_symbols:                         37
% 39.42/5.48  num_of_terms:                           221082
% 39.42/5.48  
% 39.42/5.48  ------ Preprocessing
% 39.42/5.48  
% 39.42/5.48  num_of_splits:                          0
% 39.42/5.48  num_of_split_atoms:                     0
% 39.42/5.48  num_of_reused_defs:                     0
% 39.42/5.48  num_eq_ax_congr_red:                    0
% 39.42/5.48  num_of_sem_filtered_clauses:            1
% 39.42/5.48  num_of_subtypes:                        0
% 39.42/5.48  monotx_restored_types:                  0
% 39.42/5.48  sat_num_of_epr_types:                   0
% 39.42/5.48  sat_num_of_non_cyclic_types:            0
% 39.42/5.48  sat_guarded_non_collapsed_types:        0
% 39.42/5.48  num_pure_diseq_elim:                    0
% 39.42/5.48  simp_replaced_by:                       0
% 39.42/5.48  res_preprocessed:                       35
% 39.42/5.48  prep_upred:                             0
% 39.42/5.48  prep_unflattend:                        0
% 39.42/5.48  smt_new_axioms:                         0
% 39.42/5.48  pred_elim_cands:                        1
% 39.42/5.48  pred_elim:                              0
% 39.42/5.48  pred_elim_cl:                           0
% 39.42/5.48  pred_elim_cycles:                       1
% 39.42/5.48  merged_defs:                            0
% 39.42/5.48  merged_defs_ncl:                        0
% 39.42/5.48  bin_hyper_res:                          0
% 39.42/5.48  prep_cycles:                            3
% 39.42/5.48  pred_elim_time:                         0.
% 39.42/5.48  splitting_time:                         0.
% 39.42/5.48  sem_filter_time:                        0.
% 39.42/5.48  monotx_time:                            0.
% 39.42/5.48  subtype_inf_time:                       0.
% 39.42/5.48  
% 39.42/5.48  ------ Problem properties
% 39.42/5.48  
% 39.42/5.48  clauses:                                8
% 39.42/5.48  conjectures:                            2
% 39.42/5.48  epr:                                    0
% 39.42/5.48  horn:                                   8
% 39.42/5.48  ground:                                 2
% 39.42/5.48  unary:                                  6
% 39.42/5.48  binary:                                 2
% 39.42/5.48  lits:                                   10
% 39.42/5.48  lits_eq:                                4
% 39.42/5.48  fd_pure:                                0
% 39.42/5.48  fd_pseudo:                              0
% 39.42/5.48  fd_cond:                                0
% 39.42/5.48  fd_pseudo_cond:                         0
% 39.42/5.48  ac_symbols:                             0
% 39.42/5.48  
% 39.42/5.48  ------ Propositional Solver
% 39.42/5.48  
% 39.42/5.48  prop_solver_calls:                      47
% 39.42/5.48  prop_fast_solver_calls:                 928
% 39.42/5.48  smt_solver_calls:                       0
% 39.42/5.48  smt_fast_solver_calls:                  0
% 39.42/5.48  prop_num_of_clauses:                    46773
% 39.42/5.48  prop_preprocess_simplified:             42063
% 39.42/5.48  prop_fo_subsumed:                       0
% 39.42/5.48  prop_solver_time:                       0.
% 39.42/5.48  smt_solver_time:                        0.
% 39.42/5.48  smt_fast_solver_time:                   0.
% 39.42/5.48  prop_fast_solver_time:                  0.
% 39.42/5.48  prop_unsat_core_time:                   0.005
% 39.42/5.48  
% 39.42/5.48  ------ QBF
% 39.42/5.48  
% 39.42/5.48  qbf_q_res:                              0
% 39.42/5.48  qbf_num_tautologies:                    0
% 39.42/5.48  qbf_prep_cycles:                        0
% 39.42/5.48  
% 39.42/5.48  ------ BMC1
% 39.42/5.48  
% 39.42/5.48  bmc1_current_bound:                     -1
% 39.42/5.48  bmc1_last_solved_bound:                 -1
% 39.42/5.48  bmc1_unsat_core_size:                   -1
% 39.42/5.48  bmc1_unsat_core_parents_size:           -1
% 39.42/5.48  bmc1_merge_next_fun:                    0
% 39.42/5.48  bmc1_unsat_core_clauses_time:           0.
% 39.42/5.48  
% 39.42/5.48  ------ Instantiation
% 39.42/5.48  
% 39.42/5.48  inst_num_of_clauses:                    7669
% 39.42/5.48  inst_num_in_passive:                    2735
% 39.42/5.48  inst_num_in_active:                     2425
% 39.42/5.48  inst_num_in_unprocessed:                2526
% 39.42/5.48  inst_num_of_loops:                      2615
% 39.42/5.48  inst_num_of_learning_restarts:          0
% 39.42/5.48  inst_num_moves_active_passive:          185
% 39.42/5.48  inst_lit_activity:                      0
% 39.42/5.48  inst_lit_activity_moves:                0
% 39.42/5.48  inst_num_tautologies:                   0
% 39.42/5.48  inst_num_prop_implied:                  0
% 39.42/5.48  inst_num_existing_simplified:           0
% 39.42/5.48  inst_num_eq_res_simplified:             0
% 39.42/5.48  inst_num_child_elim:                    0
% 39.42/5.48  inst_num_of_dismatching_blockings:      13512
% 39.42/5.48  inst_num_of_non_proper_insts:           18634
% 39.42/5.48  inst_num_of_duplicates:                 0
% 39.42/5.48  inst_inst_num_from_inst_to_res:         0
% 39.42/5.48  inst_dismatching_checking_time:         0.
% 39.42/5.48  
% 39.42/5.48  ------ Resolution
% 39.42/5.48  
% 39.42/5.48  res_num_of_clauses:                     0
% 39.42/5.48  res_num_in_passive:                     0
% 39.42/5.48  res_num_in_active:                      0
% 39.42/5.48  res_num_of_loops:                       38
% 39.42/5.48  res_forward_subset_subsumed:            1514
% 39.42/5.48  res_backward_subset_subsumed:           60
% 39.42/5.48  res_forward_subsumed:                   0
% 39.42/5.48  res_backward_subsumed:                  0
% 39.42/5.48  res_forward_subsumption_resolution:     0
% 39.42/5.48  res_backward_subsumption_resolution:    0
% 39.42/5.48  res_clause_to_clause_subsumption:       187843
% 39.42/5.48  res_orphan_elimination:                 0
% 39.42/5.48  res_tautology_del:                      1060
% 39.42/5.48  res_num_eq_res_simplified:              0
% 39.42/5.48  res_num_sel_changes:                    0
% 39.42/5.48  res_moves_from_active_to_pass:          0
% 39.42/5.48  
% 39.42/5.48  ------ Superposition
% 39.42/5.48  
% 39.42/5.48  sup_time_total:                         0.
% 39.42/5.48  sup_time_generating:                    0.
% 39.42/5.48  sup_time_sim_full:                      0.
% 39.42/5.48  sup_time_sim_immed:                     0.
% 39.42/5.48  
% 39.42/5.48  sup_num_of_clauses:                     9500
% 39.42/5.48  sup_num_in_active:                      384
% 39.42/5.48  sup_num_in_passive:                     9116
% 39.42/5.48  sup_num_of_loops:                       522
% 39.42/5.48  sup_fw_superposition:                   23695
% 39.42/5.48  sup_bw_superposition:                   21570
% 39.42/5.48  sup_immediate_simplified:               29192
% 39.42/5.48  sup_given_eliminated:                   8
% 39.42/5.48  comparisons_done:                       0
% 39.42/5.48  comparisons_avoided:                    0
% 39.42/5.48  
% 39.42/5.48  ------ Simplifications
% 39.42/5.48  
% 39.42/5.48  
% 39.42/5.48  sim_fw_subset_subsumed:                 46
% 39.42/5.48  sim_bw_subset_subsumed:                 0
% 39.42/5.48  sim_fw_subsumed:                        5110
% 39.42/5.48  sim_bw_subsumed:                        216
% 39.42/5.48  sim_fw_subsumption_res:                 0
% 39.42/5.48  sim_bw_subsumption_res:                 0
% 39.42/5.48  sim_tautology_del:                      134
% 39.42/5.48  sim_eq_tautology_del:                   5256
% 39.42/5.48  sim_eq_res_simp:                        0
% 39.42/5.48  sim_fw_demodulated:                     27007
% 39.42/5.48  sim_bw_demodulated:                     473
% 39.42/5.48  sim_light_normalised:                   13131
% 39.42/5.48  sim_joinable_taut:                      0
% 39.42/5.48  sim_joinable_simp:                      0
% 39.42/5.48  sim_ac_normalised:                      0
% 39.42/5.48  sim_smt_subsumption:                    0
% 39.42/5.48  
%------------------------------------------------------------------------------
