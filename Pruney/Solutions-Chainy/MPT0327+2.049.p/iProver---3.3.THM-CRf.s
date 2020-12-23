%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:05 EST 2020

% Result     : Theorem 23.73s
% Output     : CNFRefutation 23.73s
% Verified   : 
% Statistics : Number of formulae       :  146 (2165 expanded)
%              Number of clauses        :   97 ( 858 expanded)
%              Number of leaves         :   17 ( 516 expanded)
%              Depth                    :   28
%              Number of atoms          :  181 (3069 expanded)
%              Number of equality atoms :  141 (2043 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f32,f35,f35,f29])).

fof(f44,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f44,f35,f29,f47,f47])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_71,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_158,plain,
    ( X0 != X1
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | k1_zfmisc_1(k3_tarski(X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_71,c_10])).

cnf(c_159,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_152,plain,
    ( X0 != X1
    | k3_xboole_0(X1,X2) = X1
    | k1_zfmisc_1(k3_tarski(X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_153,plain,
    ( k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_205,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_159,c_153])).

cnf(c_565,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_205])).

cnf(c_1647,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_565,c_7])).

cnf(c_1658,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1647,c_7])).

cnf(c_5429,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_1658])).

cnf(c_562,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_205,c_7])).

cnf(c_1399,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_7,c_562])).

cnf(c_55794,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5429,c_1399])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_449,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_140,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_141,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_459,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_449,c_141])).

cnf(c_56196,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(X2,X3) ),
    inference(demodulation,[status(thm)],[c_55794,c_459])).

cnf(c_1410,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_562,c_7])).

cnf(c_1415,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_1410,c_7])).

cnf(c_3632,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_7,c_1415])).

cnf(c_55804,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X4,X2),k5_xboole_0(X3,k5_xboole_0(X4,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_5429,c_3632])).

cnf(c_56166,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X4,X2),k5_xboole_0(X3,X4)) ),
    inference(demodulation,[status(thm)],[c_55804,c_459])).

cnf(c_56197,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_56196,c_56166])).

cnf(c_3625,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))))) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_7,c_1415])).

cnf(c_55863,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X1)))) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5429,c_3625])).

cnf(c_55997,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X1)))) = X2 ),
    inference(demodulation,[status(thm)],[c_55863,c_459])).

cnf(c_56201,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_56197,c_55997])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_122,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_123,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_164,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X0
    | k3_xboole_0(X0,X1) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_123])).

cnf(c_165,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_279,plain,
    ( k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_165])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_704,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_279,c_5])).

cnf(c_723,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_704,c_165])).

cnf(c_1402,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[status(thm)],[c_723,c_562])).

cnf(c_1708,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_1402,c_562])).

cnf(c_561,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_278,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_141])).

cnf(c_2326,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_561,c_278])).

cnf(c_741,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[status(thm)],[c_723,c_7])).

cnf(c_1098,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_205,c_741])).

cnf(c_2732,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_1098])).

cnf(c_2747,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2732,c_723])).

cnf(c_564,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_2369,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_564,c_278])).

cnf(c_2763,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_2747,c_2369])).

cnf(c_6501,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_1708,c_2326,c_2763])).

cnf(c_3278,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_7,c_1399])).

cnf(c_19321,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6501,c_3278])).

cnf(c_20146,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_19321,c_2326])).

cnf(c_20147,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_20146,c_741])).

cnf(c_55818,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5429,c_20147])).

cnf(c_56123,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_55818,c_7])).

cnf(c_56124,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_56123,c_459])).

cnf(c_56204,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = sK1 ),
    inference(demodulation,[status(thm)],[c_56201,c_56124])).

cnf(c_28431,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X1))))) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_723,c_3625])).

cnf(c_28492,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X3))))) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[status(thm)],[c_3625,c_562])).

cnf(c_28772,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X3))))) = k5_xboole_0(X2,X3) ),
    inference(demodulation,[status(thm)],[c_28492,c_2326])).

cnf(c_28520,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k5_xboole_0(X0,X1),X4))))) = k5_xboole_0(X5,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,k5_xboole_0(k1_xboole_0,X4))))) ),
    inference(superposition,[status(thm)],[c_3625,c_3625])).

cnf(c_28699,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k5_xboole_0(X0,X1),X4))))) = k5_xboole_0(X5,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,X4)))) ),
    inference(demodulation,[status(thm)],[c_28520,c_2326])).

cnf(c_28773,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(demodulation,[status(thm)],[c_28772,c_28699])).

cnf(c_1404,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[status(thm)],[c_741,c_562])).

cnf(c_28531,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[status(thm)],[c_3625,c_1404])).

cnf(c_28663,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_28531,c_7])).

cnf(c_28664,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X2) ),
    inference(demodulation,[status(thm)],[c_28663,c_2326])).

cnf(c_28786,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0),X1)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X1) ),
    inference(demodulation,[status(thm)],[c_28773,c_28664])).

cnf(c_1646,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_565,c_7])).

cnf(c_5164,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) ),
    inference(superposition,[status(thm)],[c_741,c_1646])).

cnf(c_28532,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[status(thm)],[c_3625,c_5164])).

cnf(c_28659,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_28532,c_7])).

cnf(c_28660,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,X2) ),
    inference(demodulation,[status(thm)],[c_28659,c_2326])).

cnf(c_28787,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0),X1)))) = k5_xboole_0(sK1,X1) ),
    inference(demodulation,[status(thm)],[c_28773,c_28660])).

cnf(c_28809,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0) = k5_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_28786,c_28787])).

cnf(c_28977,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_28431,c_28773,c_28809])).

cnf(c_55816,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5429,c_28977])).

cnf(c_56130,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_55816,c_7])).

cnf(c_56131,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_56130,c_459])).

cnf(c_56213,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1 ),
    inference(demodulation,[status(thm)],[c_56204,c_56131])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_271,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_345,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_279,c_271])).

cnf(c_557,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_7,c_345])).

cnf(c_558,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_557,c_205])).

cnf(c_860,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(superposition,[status(thm)],[c_7,c_558])).

cnf(c_2329,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_2326,c_860])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56213,c_2329])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:15:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 23.73/3.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.73/3.47  
% 23.73/3.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.73/3.47  
% 23.73/3.47  ------  iProver source info
% 23.73/3.47  
% 23.73/3.47  git: date: 2020-06-30 10:37:57 +0100
% 23.73/3.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.73/3.47  git: non_committed_changes: false
% 23.73/3.47  git: last_make_outside_of_git: false
% 23.73/3.47  
% 23.73/3.47  ------ 
% 23.73/3.47  ------ Parsing...
% 23.73/3.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.73/3.47  
% 23.73/3.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 23.73/3.47  
% 23.73/3.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.73/3.47  
% 23.73/3.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.47  ------ Proving...
% 23.73/3.47  ------ Problem Properties 
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  clauses                                 13
% 23.73/3.47  conjectures                             1
% 23.73/3.47  EPR                                     0
% 23.73/3.47  Horn                                    13
% 23.73/3.47  unary                                   12
% 23.73/3.47  binary                                  1
% 23.73/3.47  lits                                    14
% 23.73/3.47  lits eq                                 14
% 23.73/3.47  fd_pure                                 0
% 23.73/3.47  fd_pseudo                               0
% 23.73/3.47  fd_cond                                 0
% 23.73/3.47  fd_pseudo_cond                          0
% 23.73/3.47  AC symbols                              0
% 23.73/3.47  
% 23.73/3.47  ------ Input Options Time Limit: Unbounded
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  ------ 
% 23.73/3.47  Current options:
% 23.73/3.47  ------ 
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  ------ Proving...
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  % SZS status Theorem for theBenchmark.p
% 23.73/3.47  
% 23.73/3.47  % SZS output start CNFRefutation for theBenchmark.p
% 23.73/3.47  
% 23.73/3.47  fof(f8,axiom,(
% 23.73/3.47    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f34,plain,(
% 23.73/3.47    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f8])).
% 23.73/3.47  
% 23.73/3.47  fof(f2,axiom,(
% 23.73/3.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f23,plain,(
% 23.73/3.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.73/3.47    inference(nnf_transformation,[],[f2])).
% 23.73/3.47  
% 23.73/3.47  fof(f28,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f23])).
% 23.73/3.47  
% 23.73/3.47  fof(f3,axiom,(
% 23.73/3.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f29,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.73/3.47    inference(cnf_transformation,[],[f3])).
% 23.73/3.47  
% 23.73/3.47  fof(f48,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 23.73/3.47    inference(definition_unfolding,[],[f28,f29])).
% 23.73/3.47  
% 23.73/3.47  fof(f16,axiom,(
% 23.73/3.47    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f42,plain,(
% 23.73/3.47    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 23.73/3.47    inference(cnf_transformation,[],[f16])).
% 23.73/3.47  
% 23.73/3.47  fof(f4,axiom,(
% 23.73/3.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f20,plain,(
% 23.73/3.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.73/3.47    inference(ennf_transformation,[],[f4])).
% 23.73/3.47  
% 23.73/3.47  fof(f30,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f20])).
% 23.73/3.47  
% 23.73/3.47  fof(f1,axiom,(
% 23.73/3.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f26,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f1])).
% 23.73/3.47  
% 23.73/3.47  fof(f7,axiom,(
% 23.73/3.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f33,plain,(
% 23.73/3.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.73/3.47    inference(cnf_transformation,[],[f7])).
% 23.73/3.47  
% 23.73/3.47  fof(f51,plain,(
% 23.73/3.47    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 23.73/3.47    inference(definition_unfolding,[],[f33,f29])).
% 23.73/3.47  
% 23.73/3.47  fof(f5,axiom,(
% 23.73/3.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f31,plain,(
% 23.73/3.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f5])).
% 23.73/3.47  
% 23.73/3.47  fof(f14,axiom,(
% 23.73/3.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f19,plain,(
% 23.73/3.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 23.73/3.47    inference(unused_predicate_definition_removal,[],[f14])).
% 23.73/3.47  
% 23.73/3.47  fof(f21,plain,(
% 23.73/3.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 23.73/3.47    inference(ennf_transformation,[],[f19])).
% 23.73/3.47  
% 23.73/3.47  fof(f40,plain,(
% 23.73/3.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f21])).
% 23.73/3.47  
% 23.73/3.47  fof(f10,axiom,(
% 23.73/3.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f36,plain,(
% 23.73/3.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f10])).
% 23.73/3.47  
% 23.73/3.47  fof(f11,axiom,(
% 23.73/3.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f37,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f11])).
% 23.73/3.47  
% 23.73/3.47  fof(f12,axiom,(
% 23.73/3.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f38,plain,(
% 23.73/3.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f12])).
% 23.73/3.47  
% 23.73/3.47  fof(f13,axiom,(
% 23.73/3.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f39,plain,(
% 23.73/3.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f13])).
% 23.73/3.47  
% 23.73/3.47  fof(f45,plain,(
% 23.73/3.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 23.73/3.47    inference(definition_unfolding,[],[f38,f39])).
% 23.73/3.47  
% 23.73/3.47  fof(f46,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 23.73/3.47    inference(definition_unfolding,[],[f37,f45])).
% 23.73/3.47  
% 23.73/3.47  fof(f47,plain,(
% 23.73/3.47    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 23.73/3.47    inference(definition_unfolding,[],[f36,f46])).
% 23.73/3.47  
% 23.73/3.47  fof(f52,plain,(
% 23.73/3.47    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 23.73/3.47    inference(definition_unfolding,[],[f40,f47])).
% 23.73/3.47  
% 23.73/3.47  fof(f17,conjecture,(
% 23.73/3.47    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f18,negated_conjecture,(
% 23.73/3.47    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 23.73/3.47    inference(negated_conjecture,[],[f17])).
% 23.73/3.47  
% 23.73/3.47  fof(f22,plain,(
% 23.73/3.47    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 23.73/3.47    inference(ennf_transformation,[],[f18])).
% 23.73/3.47  
% 23.73/3.47  fof(f24,plain,(
% 23.73/3.47    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 23.73/3.47    introduced(choice_axiom,[])).
% 23.73/3.47  
% 23.73/3.47  fof(f25,plain,(
% 23.73/3.47    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 23.73/3.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).
% 23.73/3.47  
% 23.73/3.47  fof(f43,plain,(
% 23.73/3.47    r2_hidden(sK0,sK1)),
% 23.73/3.47    inference(cnf_transformation,[],[f25])).
% 23.73/3.47  
% 23.73/3.47  fof(f6,axiom,(
% 23.73/3.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f32,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.73/3.47    inference(cnf_transformation,[],[f6])).
% 23.73/3.47  
% 23.73/3.47  fof(f9,axiom,(
% 23.73/3.47    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 23.73/3.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.47  
% 23.73/3.47  fof(f35,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 23.73/3.47    inference(cnf_transformation,[],[f9])).
% 23.73/3.47  
% 23.73/3.47  fof(f50,plain,(
% 23.73/3.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 23.73/3.47    inference(definition_unfolding,[],[f32,f35,f35,f29])).
% 23.73/3.47  
% 23.73/3.47  fof(f44,plain,(
% 23.73/3.47    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 23.73/3.47    inference(cnf_transformation,[],[f25])).
% 23.73/3.47  
% 23.73/3.47  fof(f54,plain,(
% 23.73/3.47    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1),
% 23.73/3.47    inference(definition_unfolding,[],[f44,f35,f29,f47,f47])).
% 23.73/3.47  
% 23.73/3.47  cnf(c_7,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.73/3.47      inference(cnf_transformation,[],[f34]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1,plain,
% 23.73/3.47      ( ~ r1_tarski(X0,X1)
% 23.73/3.47      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.73/3.47      inference(cnf_transformation,[],[f48]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_71,plain,
% 23.73/3.47      ( ~ r1_tarski(X0,X1)
% 23.73/3.47      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.73/3.47      inference(prop_impl,[status(thm)],[c_1]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_10,plain,
% 23.73/3.47      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 23.73/3.47      inference(cnf_transformation,[],[f42]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_158,plain,
% 23.73/3.47      ( X0 != X1
% 23.73/3.47      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
% 23.73/3.47      | k1_zfmisc_1(k3_tarski(X0)) != X2 ),
% 23.73/3.47      inference(resolution_lifted,[status(thm)],[c_71,c_10]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_159,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = k1_xboole_0 ),
% 23.73/3.47      inference(unflattening,[status(thm)],[c_158]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_3,plain,
% 23.73/3.47      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.73/3.47      inference(cnf_transformation,[],[f30]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_152,plain,
% 23.73/3.47      ( X0 != X1
% 23.73/3.47      | k3_xboole_0(X1,X2) = X1
% 23.73/3.47      | k1_zfmisc_1(k3_tarski(X0)) != X2 ),
% 23.73/3.47      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_153,plain,
% 23.73/3.47      ( k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
% 23.73/3.47      inference(unflattening,[status(thm)],[c_152]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_205,plain,
% 23.73/3.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_159,c_153]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_565,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_205]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1647,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k1_xboole_0 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_565,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1658,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k1_xboole_0 ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_1647,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_5429,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k1_xboole_0 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_1658]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_562,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_205,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1399,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_562]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55794,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_5429,c_1399]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_0,plain,
% 23.73/3.47      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.73/3.47      inference(cnf_transformation,[],[f26]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_6,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 23.73/3.47      inference(cnf_transformation,[],[f51]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_449,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_4,plain,
% 23.73/3.47      ( r1_tarski(k1_xboole_0,X0) ),
% 23.73/3.47      inference(cnf_transformation,[],[f31]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_140,plain,
% 23.73/3.47      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 23.73/3.47      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_141,plain,
% 23.73/3.47      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.73/3.47      inference(unflattening,[status(thm)],[c_140]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_459,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_449,c_141]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56196,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(X2,X3) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_55794,c_459]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1410,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_562,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1415,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_1410,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_3632,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = k5_xboole_0(k1_xboole_0,X3) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_1415]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55804,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X4,X2),k5_xboole_0(X3,k5_xboole_0(X4,k1_xboole_0))) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_5429,c_3632]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56166,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X3,X0),X1))))) = k5_xboole_0(k5_xboole_0(X4,X2),k5_xboole_0(X3,X4)) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_55804,c_459]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56197,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X1,X2) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56196,c_56166]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_3625,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))))) = k5_xboole_0(k1_xboole_0,X3) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_1415]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55863,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X1)))) = k5_xboole_0(X2,k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_5429,c_3625]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55997,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X1)))) = X2 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_55863,c_459]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56201,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56197,c_55997]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_8,plain,
% 23.73/3.47      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 23.73/3.47      inference(cnf_transformation,[],[f52]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_12,negated_conjecture,
% 23.73/3.47      ( r2_hidden(sK0,sK1) ),
% 23.73/3.47      inference(cnf_transformation,[],[f43]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_122,plain,
% 23.73/3.47      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 23.73/3.47      | sK0 != X0
% 23.73/3.47      | sK1 != X1 ),
% 23.73/3.47      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_123,plain,
% 23.73/3.47      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 23.73/3.47      inference(unflattening,[status(thm)],[c_122]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_164,plain,
% 23.73/3.47      ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != X0
% 23.73/3.47      | k3_xboole_0(X0,X1) = X0
% 23.73/3.47      | sK1 != X1 ),
% 23.73/3.47      inference(resolution_lifted,[status(thm)],[c_3,c_123]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_165,plain,
% 23.73/3.47      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 23.73/3.47      inference(unflattening,[status(thm)],[c_164]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_279,plain,
% 23.73/3.47      ( k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_0,c_165]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_5,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 23.73/3.47      inference(cnf_transformation,[],[f50]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_704,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_279,c_5]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_723,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_704,c_165]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1402,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_723,c_562]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1708,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_1402,c_562]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_561,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) = k5_xboole_0(X0,X1) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_278,plain,
% 23.73/3.47      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_0,c_141]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2326,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_561,c_278]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_741,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_723,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1098,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_205,c_741]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2732,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_1098]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2747,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_2732,c_723]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_564,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) = k5_xboole_0(X0,X1) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2369,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X0,X1) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_564,c_278]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2763,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_2747,c_2369]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_6501,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_1708,c_2326,c_2763]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_3278,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k1_xboole_0,X3) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_1399]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_19321,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)))) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_6501,c_3278]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_20146,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_19321,c_2326]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_20147,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_20146,c_741]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55818,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_5429,c_20147]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56123,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_55818,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56124,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56123,c_459]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56204,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56201,c_56124]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28431,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X1))))) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_723,c_3625]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28492,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X3))))) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,X3)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_3625,c_562]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28772,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X3))))) = k5_xboole_0(X2,X3) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28492,c_2326]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28520,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k5_xboole_0(X0,X1),X4))))) = k5_xboole_0(X5,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,k5_xboole_0(k1_xboole_0,X4))))) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_3625,c_3625]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28699,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(k5_xboole_0(X0,X1),X4))))) = k5_xboole_0(X5,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X5,X4)))) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28520,c_2326]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28773,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28772,c_28699]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1404,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_741,c_562]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28531,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,X2)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_3625,c_1404]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28663,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k1_xboole_0,X2)) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_28531,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28664,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X2) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28663,c_2326]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28786,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0),X1)))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X1) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28773,c_28664]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_1646,plain,
% 23.73/3.47      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_565,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_5164,plain,
% 23.73/3.47      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_741,c_1646]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28532,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X2)) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_3625,c_5164]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28659,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X2)) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_28532,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28660,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,X2) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28659,c_2326]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28787,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0),X1)))) = k5_xboole_0(sK1,X1) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28773,c_28660]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28809,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0) = k5_xboole_0(sK1,X0) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_28786,c_28787]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_28977,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_28431,c_28773,c_28809]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_55816,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_5429,c_28977]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56130,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),k1_xboole_0) ),
% 23.73/3.47      inference(light_normalisation,[status(thm)],[c_55816,c_7]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56131,plain,
% 23.73/3.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56130,c_459]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_56213,plain,
% 23.73/3.47      ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_56204,c_56131]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_11,negated_conjecture,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 23.73/3.47      inference(cnf_transformation,[],[f54]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_271,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_345,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_279,c_271]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_557,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_7,c_345]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_558,plain,
% 23.73/3.47      ( k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_557,c_205]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_860,plain,
% 23.73/3.47      ( k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 23.73/3.47      inference(superposition,[status(thm)],[c_7,c_558]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(c_2329,plain,
% 23.73/3.47      ( k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 23.73/3.47      inference(demodulation,[status(thm)],[c_2326,c_860]) ).
% 23.73/3.47  
% 23.73/3.47  cnf(contradiction,plain,
% 23.73/3.47      ( $false ),
% 23.73/3.47      inference(minisat,[status(thm)],[c_56213,c_2329]) ).
% 23.73/3.47  
% 23.73/3.47  
% 23.73/3.47  % SZS output end CNFRefutation for theBenchmark.p
% 23.73/3.47  
% 23.73/3.47  ------                               Statistics
% 23.73/3.47  
% 23.73/3.47  ------ Selected
% 23.73/3.47  
% 23.73/3.47  total_time:                             2.978
% 23.73/3.47  
%------------------------------------------------------------------------------
