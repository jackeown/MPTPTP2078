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
% DateTime   : Thu Dec  3 11:24:30 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :   65 (  79 expanded)
%              Number of clauses        :   42 (  49 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 172 expanded)
%              Number of equality atoms :   82 ( 103 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_315,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
    | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_17116,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
    | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7101,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_454,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
    | k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != X1
    | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != X0 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_717,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
    | ~ r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X1)
    | k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != X1
    | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_3297,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
    | ~ r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
    | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X2)
    | X2 != X1
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_698,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),X0)
    | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X1)
    | X1 != X0
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1343,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1))
    | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0)
    | X0 != k3_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1345,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1))
    | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_984,plain,
    ( r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_345,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_342,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_161,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_214,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X0
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_295,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_237,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_271,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_218,plain,
    ( X0 != X1
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X1
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_229,plain,
    ( X0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = X0
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_256,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_254,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_160,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_246,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_169,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_113,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_55,c_8])).

cnf(c_114,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_53,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_108,plain,
    ( k4_xboole_0(sK1,sK2) != X0
    | k3_xboole_0(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_53,c_7])).

cnf(c_109,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17116,c_7101,c_3297,c_1345,c_984,c_345,c_342,c_295,c_271,c_256,c_254,c_246,c_169,c_114,c_109])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.64/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.50  
% 7.64/1.50  ------  iProver source info
% 7.64/1.50  
% 7.64/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.50  git: non_committed_changes: false
% 7.64/1.50  git: last_make_outside_of_git: false
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options
% 7.64/1.50  
% 7.64/1.50  --out_options                           all
% 7.64/1.50  --tptp_safe_out                         true
% 7.64/1.50  --problem_path                          ""
% 7.64/1.50  --include_path                          ""
% 7.64/1.50  --clausifier                            res/vclausify_rel
% 7.64/1.50  --clausifier_options                    ""
% 7.64/1.50  --stdin                                 false
% 7.64/1.50  --stats_out                             all
% 7.64/1.50  
% 7.64/1.50  ------ General Options
% 7.64/1.50  
% 7.64/1.50  --fof                                   false
% 7.64/1.50  --time_out_real                         305.
% 7.64/1.50  --time_out_virtual                      -1.
% 7.64/1.50  --symbol_type_check                     false
% 7.64/1.50  --clausify_out                          false
% 7.64/1.50  --sig_cnt_out                           false
% 7.64/1.50  --trig_cnt_out                          false
% 7.64/1.50  --trig_cnt_out_tolerance                1.
% 7.64/1.50  --trig_cnt_out_sk_spl                   false
% 7.64/1.50  --abstr_cl_out                          false
% 7.64/1.50  
% 7.64/1.50  ------ Global Options
% 7.64/1.50  
% 7.64/1.50  --schedule                              default
% 7.64/1.50  --add_important_lit                     false
% 7.64/1.50  --prop_solver_per_cl                    1000
% 7.64/1.50  --min_unsat_core                        false
% 7.64/1.50  --soft_assumptions                      false
% 7.64/1.50  --soft_lemma_size                       3
% 7.64/1.50  --prop_impl_unit_size                   0
% 7.64/1.50  --prop_impl_unit                        []
% 7.64/1.50  --share_sel_clauses                     true
% 7.64/1.50  --reset_solvers                         false
% 7.64/1.50  --bc_imp_inh                            [conj_cone]
% 7.64/1.50  --conj_cone_tolerance                   3.
% 7.64/1.50  --extra_neg_conj                        none
% 7.64/1.50  --large_theory_mode                     true
% 7.64/1.50  --prolific_symb_bound                   200
% 7.64/1.50  --lt_threshold                          2000
% 7.64/1.50  --clause_weak_htbl                      true
% 7.64/1.50  --gc_record_bc_elim                     false
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing Options
% 7.64/1.50  
% 7.64/1.50  --preprocessing_flag                    true
% 7.64/1.50  --time_out_prep_mult                    0.1
% 7.64/1.50  --splitting_mode                        input
% 7.64/1.50  --splitting_grd                         true
% 7.64/1.50  --splitting_cvd                         false
% 7.64/1.50  --splitting_cvd_svl                     false
% 7.64/1.50  --splitting_nvd                         32
% 7.64/1.50  --sub_typing                            true
% 7.64/1.50  --prep_gs_sim                           true
% 7.64/1.50  --prep_unflatten                        true
% 7.64/1.50  --prep_res_sim                          true
% 7.64/1.50  --prep_upred                            true
% 7.64/1.50  --prep_sem_filter                       exhaustive
% 7.64/1.50  --prep_sem_filter_out                   false
% 7.64/1.50  --pred_elim                             true
% 7.64/1.50  --res_sim_input                         true
% 7.64/1.50  --eq_ax_congr_red                       true
% 7.64/1.50  --pure_diseq_elim                       true
% 7.64/1.50  --brand_transform                       false
% 7.64/1.50  --non_eq_to_eq                          false
% 7.64/1.50  --prep_def_merge                        true
% 7.64/1.50  --prep_def_merge_prop_impl              false
% 7.64/1.50  --prep_def_merge_mbd                    true
% 7.64/1.50  --prep_def_merge_tr_red                 false
% 7.64/1.50  --prep_def_merge_tr_cl                  false
% 7.64/1.50  --smt_preprocessing                     true
% 7.64/1.50  --smt_ac_axioms                         fast
% 7.64/1.50  --preprocessed_out                      false
% 7.64/1.50  --preprocessed_stats                    false
% 7.64/1.50  
% 7.64/1.50  ------ Abstraction refinement Options
% 7.64/1.50  
% 7.64/1.50  --abstr_ref                             []
% 7.64/1.50  --abstr_ref_prep                        false
% 7.64/1.50  --abstr_ref_until_sat                   false
% 7.64/1.50  --abstr_ref_sig_restrict                funpre
% 7.64/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.50  --abstr_ref_under                       []
% 7.64/1.50  
% 7.64/1.50  ------ SAT Options
% 7.64/1.50  
% 7.64/1.50  --sat_mode                              false
% 7.64/1.50  --sat_fm_restart_options                ""
% 7.64/1.50  --sat_gr_def                            false
% 7.64/1.50  --sat_epr_types                         true
% 7.64/1.50  --sat_non_cyclic_types                  false
% 7.64/1.50  --sat_finite_models                     false
% 7.64/1.50  --sat_fm_lemmas                         false
% 7.64/1.50  --sat_fm_prep                           false
% 7.64/1.50  --sat_fm_uc_incr                        true
% 7.64/1.50  --sat_out_model                         small
% 7.64/1.50  --sat_out_clauses                       false
% 7.64/1.50  
% 7.64/1.50  ------ QBF Options
% 7.64/1.50  
% 7.64/1.50  --qbf_mode                              false
% 7.64/1.50  --qbf_elim_univ                         false
% 7.64/1.50  --qbf_dom_inst                          none
% 7.64/1.50  --qbf_dom_pre_inst                      false
% 7.64/1.50  --qbf_sk_in                             false
% 7.64/1.50  --qbf_pred_elim                         true
% 7.64/1.50  --qbf_split                             512
% 7.64/1.50  
% 7.64/1.50  ------ BMC1 Options
% 7.64/1.50  
% 7.64/1.50  --bmc1_incremental                      false
% 7.64/1.50  --bmc1_axioms                           reachable_all
% 7.64/1.50  --bmc1_min_bound                        0
% 7.64/1.50  --bmc1_max_bound                        -1
% 7.64/1.50  --bmc1_max_bound_default                -1
% 7.64/1.50  --bmc1_symbol_reachability              true
% 7.64/1.50  --bmc1_property_lemmas                  false
% 7.64/1.50  --bmc1_k_induction                      false
% 7.64/1.50  --bmc1_non_equiv_states                 false
% 7.64/1.50  --bmc1_deadlock                         false
% 7.64/1.50  --bmc1_ucm                              false
% 7.64/1.50  --bmc1_add_unsat_core                   none
% 7.64/1.50  --bmc1_unsat_core_children              false
% 7.64/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.50  --bmc1_out_stat                         full
% 7.64/1.50  --bmc1_ground_init                      false
% 7.64/1.50  --bmc1_pre_inst_next_state              false
% 7.64/1.50  --bmc1_pre_inst_state                   false
% 7.64/1.50  --bmc1_pre_inst_reach_state             false
% 7.64/1.50  --bmc1_out_unsat_core                   false
% 7.64/1.50  --bmc1_aig_witness_out                  false
% 7.64/1.50  --bmc1_verbose                          false
% 7.64/1.50  --bmc1_dump_clauses_tptp                false
% 7.64/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.50  --bmc1_dump_file                        -
% 7.64/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.50  --bmc1_ucm_extend_mode                  1
% 7.64/1.50  --bmc1_ucm_init_mode                    2
% 7.64/1.50  --bmc1_ucm_cone_mode                    none
% 7.64/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.50  --bmc1_ucm_relax_model                  4
% 7.64/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.50  --bmc1_ucm_layered_model                none
% 7.64/1.50  --bmc1_ucm_max_lemma_size               10
% 7.64/1.50  
% 7.64/1.50  ------ AIG Options
% 7.64/1.50  
% 7.64/1.50  --aig_mode                              false
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation Options
% 7.64/1.50  
% 7.64/1.50  --instantiation_flag                    true
% 7.64/1.50  --inst_sos_flag                         true
% 7.64/1.50  --inst_sos_phase                        true
% 7.64/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel_side                     num_symb
% 7.64/1.50  --inst_solver_per_active                1400
% 7.64/1.50  --inst_solver_calls_frac                1.
% 7.64/1.50  --inst_passive_queue_type               priority_queues
% 7.64/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.50  --inst_passive_queues_freq              [25;2]
% 7.64/1.50  --inst_dismatching                      true
% 7.64/1.50  --inst_eager_unprocessed_to_passive     true
% 7.64/1.50  --inst_prop_sim_given                   true
% 7.64/1.50  --inst_prop_sim_new                     false
% 7.64/1.50  --inst_subs_new                         false
% 7.64/1.50  --inst_eq_res_simp                      false
% 7.64/1.50  --inst_subs_given                       false
% 7.64/1.50  --inst_orphan_elimination               true
% 7.64/1.50  --inst_learning_loop_flag               true
% 7.64/1.50  --inst_learning_start                   3000
% 7.64/1.50  --inst_learning_factor                  2
% 7.64/1.50  --inst_start_prop_sim_after_learn       3
% 7.64/1.50  --inst_sel_renew                        solver
% 7.64/1.50  --inst_lit_activity_flag                true
% 7.64/1.50  --inst_restr_to_given                   false
% 7.64/1.50  --inst_activity_threshold               500
% 7.64/1.50  --inst_out_proof                        true
% 7.64/1.50  
% 7.64/1.50  ------ Resolution Options
% 7.64/1.50  
% 7.64/1.50  --resolution_flag                       true
% 7.64/1.50  --res_lit_sel                           adaptive
% 7.64/1.50  --res_lit_sel_side                      none
% 7.64/1.50  --res_ordering                          kbo
% 7.64/1.50  --res_to_prop_solver                    active
% 7.64/1.50  --res_prop_simpl_new                    false
% 7.64/1.50  --res_prop_simpl_given                  true
% 7.64/1.50  --res_passive_queue_type                priority_queues
% 7.64/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.50  --res_passive_queues_freq               [15;5]
% 7.64/1.50  --res_forward_subs                      full
% 7.64/1.50  --res_backward_subs                     full
% 7.64/1.50  --res_forward_subs_resolution           true
% 7.64/1.50  --res_backward_subs_resolution          true
% 7.64/1.50  --res_orphan_elimination                true
% 7.64/1.50  --res_time_limit                        2.
% 7.64/1.50  --res_out_proof                         true
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Options
% 7.64/1.50  
% 7.64/1.50  --superposition_flag                    true
% 7.64/1.50  --sup_passive_queue_type                priority_queues
% 7.64/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.50  --demod_completeness_check              fast
% 7.64/1.50  --demod_use_ground                      true
% 7.64/1.50  --sup_to_prop_solver                    passive
% 7.64/1.50  --sup_prop_simpl_new                    true
% 7.64/1.50  --sup_prop_simpl_given                  true
% 7.64/1.50  --sup_fun_splitting                     true
% 7.64/1.50  --sup_smt_interval                      50000
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Simplification Setup
% 7.64/1.50  
% 7.64/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.50  --sup_immed_triv                        [TrivRules]
% 7.64/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_bw_main                     []
% 7.64/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_input_bw                          []
% 7.64/1.50  
% 7.64/1.50  ------ Combination Options
% 7.64/1.50  
% 7.64/1.50  --comb_res_mult                         3
% 7.64/1.50  --comb_sup_mult                         2
% 7.64/1.50  --comb_inst_mult                        10
% 7.64/1.50  
% 7.64/1.50  ------ Debug Options
% 7.64/1.50  
% 7.64/1.50  --dbg_backtrace                         false
% 7.64/1.50  --dbg_dump_prop_clauses                 false
% 7.64/1.50  --dbg_dump_prop_clauses_file            -
% 7.64/1.50  --dbg_out_stat                          false
% 7.64/1.50  ------ Parsing...
% 7.64/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.50  ------ Proving...
% 7.64/1.50  ------ Problem Properties 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  clauses                                 8
% 7.64/1.50  conjectures                             0
% 7.64/1.50  EPR                                     0
% 7.64/1.50  Horn                                    8
% 7.64/1.50  unary                                   7
% 7.64/1.50  binary                                  1
% 7.64/1.50  lits                                    9
% 7.64/1.50  lits eq                                 7
% 7.64/1.50  fd_pure                                 0
% 7.64/1.50  fd_pseudo                               0
% 7.64/1.50  fd_cond                                 1
% 7.64/1.50  fd_pseudo_cond                          0
% 7.64/1.50  AC symbols                              0
% 7.64/1.50  
% 7.64/1.50  ------ Schedule dynamic 5 is on 
% 7.64/1.50  
% 7.64/1.50  ------ no conjectures: strip conj schedule 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  Current options:
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  ------ Input Options
% 7.64/1.50  
% 7.64/1.50  --out_options                           all
% 7.64/1.50  --tptp_safe_out                         true
% 7.64/1.50  --problem_path                          ""
% 7.64/1.50  --include_path                          ""
% 7.64/1.50  --clausifier                            res/vclausify_rel
% 7.64/1.50  --clausifier_options                    ""
% 7.64/1.50  --stdin                                 false
% 7.64/1.50  --stats_out                             all
% 7.64/1.50  
% 7.64/1.50  ------ General Options
% 7.64/1.50  
% 7.64/1.50  --fof                                   false
% 7.64/1.50  --time_out_real                         305.
% 7.64/1.50  --time_out_virtual                      -1.
% 7.64/1.50  --symbol_type_check                     false
% 7.64/1.50  --clausify_out                          false
% 7.64/1.50  --sig_cnt_out                           false
% 7.64/1.50  --trig_cnt_out                          false
% 7.64/1.50  --trig_cnt_out_tolerance                1.
% 7.64/1.50  --trig_cnt_out_sk_spl                   false
% 7.64/1.50  --abstr_cl_out                          false
% 7.64/1.50  
% 7.64/1.50  ------ Global Options
% 7.64/1.50  
% 7.64/1.50  --schedule                              default
% 7.64/1.50  --add_important_lit                     false
% 7.64/1.50  --prop_solver_per_cl                    1000
% 7.64/1.50  --min_unsat_core                        false
% 7.64/1.50  --soft_assumptions                      false
% 7.64/1.50  --soft_lemma_size                       3
% 7.64/1.50  --prop_impl_unit_size                   0
% 7.64/1.50  --prop_impl_unit                        []
% 7.64/1.50  --share_sel_clauses                     true
% 7.64/1.50  --reset_solvers                         false
% 7.64/1.50  --bc_imp_inh                            [conj_cone]
% 7.64/1.50  --conj_cone_tolerance                   3.
% 7.64/1.50  --extra_neg_conj                        none
% 7.64/1.50  --large_theory_mode                     true
% 7.64/1.50  --prolific_symb_bound                   200
% 7.64/1.50  --lt_threshold                          2000
% 7.64/1.50  --clause_weak_htbl                      true
% 7.64/1.50  --gc_record_bc_elim                     false
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing Options
% 7.64/1.50  
% 7.64/1.50  --preprocessing_flag                    true
% 7.64/1.50  --time_out_prep_mult                    0.1
% 7.64/1.50  --splitting_mode                        input
% 7.64/1.50  --splitting_grd                         true
% 7.64/1.50  --splitting_cvd                         false
% 7.64/1.50  --splitting_cvd_svl                     false
% 7.64/1.50  --splitting_nvd                         32
% 7.64/1.50  --sub_typing                            true
% 7.64/1.50  --prep_gs_sim                           true
% 7.64/1.50  --prep_unflatten                        true
% 7.64/1.50  --prep_res_sim                          true
% 7.64/1.50  --prep_upred                            true
% 7.64/1.50  --prep_sem_filter                       exhaustive
% 7.64/1.50  --prep_sem_filter_out                   false
% 7.64/1.50  --pred_elim                             true
% 7.64/1.50  --res_sim_input                         true
% 7.64/1.50  --eq_ax_congr_red                       true
% 7.64/1.50  --pure_diseq_elim                       true
% 7.64/1.50  --brand_transform                       false
% 7.64/1.50  --non_eq_to_eq                          false
% 7.64/1.50  --prep_def_merge                        true
% 7.64/1.50  --prep_def_merge_prop_impl              false
% 7.64/1.50  --prep_def_merge_mbd                    true
% 7.64/1.50  --prep_def_merge_tr_red                 false
% 7.64/1.50  --prep_def_merge_tr_cl                  false
% 7.64/1.50  --smt_preprocessing                     true
% 7.64/1.50  --smt_ac_axioms                         fast
% 7.64/1.50  --preprocessed_out                      false
% 7.64/1.50  --preprocessed_stats                    false
% 7.64/1.50  
% 7.64/1.50  ------ Abstraction refinement Options
% 7.64/1.50  
% 7.64/1.50  --abstr_ref                             []
% 7.64/1.50  --abstr_ref_prep                        false
% 7.64/1.50  --abstr_ref_until_sat                   false
% 7.64/1.50  --abstr_ref_sig_restrict                funpre
% 7.64/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.50  --abstr_ref_under                       []
% 7.64/1.50  
% 7.64/1.50  ------ SAT Options
% 7.64/1.50  
% 7.64/1.50  --sat_mode                              false
% 7.64/1.50  --sat_fm_restart_options                ""
% 7.64/1.50  --sat_gr_def                            false
% 7.64/1.50  --sat_epr_types                         true
% 7.64/1.50  --sat_non_cyclic_types                  false
% 7.64/1.50  --sat_finite_models                     false
% 7.64/1.50  --sat_fm_lemmas                         false
% 7.64/1.50  --sat_fm_prep                           false
% 7.64/1.50  --sat_fm_uc_incr                        true
% 7.64/1.50  --sat_out_model                         small
% 7.64/1.50  --sat_out_clauses                       false
% 7.64/1.50  
% 7.64/1.50  ------ QBF Options
% 7.64/1.50  
% 7.64/1.50  --qbf_mode                              false
% 7.64/1.50  --qbf_elim_univ                         false
% 7.64/1.50  --qbf_dom_inst                          none
% 7.64/1.50  --qbf_dom_pre_inst                      false
% 7.64/1.50  --qbf_sk_in                             false
% 7.64/1.50  --qbf_pred_elim                         true
% 7.64/1.50  --qbf_split                             512
% 7.64/1.50  
% 7.64/1.50  ------ BMC1 Options
% 7.64/1.50  
% 7.64/1.50  --bmc1_incremental                      false
% 7.64/1.50  --bmc1_axioms                           reachable_all
% 7.64/1.50  --bmc1_min_bound                        0
% 7.64/1.50  --bmc1_max_bound                        -1
% 7.64/1.50  --bmc1_max_bound_default                -1
% 7.64/1.50  --bmc1_symbol_reachability              true
% 7.64/1.50  --bmc1_property_lemmas                  false
% 7.64/1.50  --bmc1_k_induction                      false
% 7.64/1.50  --bmc1_non_equiv_states                 false
% 7.64/1.50  --bmc1_deadlock                         false
% 7.64/1.50  --bmc1_ucm                              false
% 7.64/1.50  --bmc1_add_unsat_core                   none
% 7.64/1.50  --bmc1_unsat_core_children              false
% 7.64/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.50  --bmc1_out_stat                         full
% 7.64/1.50  --bmc1_ground_init                      false
% 7.64/1.50  --bmc1_pre_inst_next_state              false
% 7.64/1.50  --bmc1_pre_inst_state                   false
% 7.64/1.50  --bmc1_pre_inst_reach_state             false
% 7.64/1.50  --bmc1_out_unsat_core                   false
% 7.64/1.50  --bmc1_aig_witness_out                  false
% 7.64/1.50  --bmc1_verbose                          false
% 7.64/1.50  --bmc1_dump_clauses_tptp                false
% 7.64/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.50  --bmc1_dump_file                        -
% 7.64/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.50  --bmc1_ucm_extend_mode                  1
% 7.64/1.50  --bmc1_ucm_init_mode                    2
% 7.64/1.50  --bmc1_ucm_cone_mode                    none
% 7.64/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.50  --bmc1_ucm_relax_model                  4
% 7.64/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.50  --bmc1_ucm_layered_model                none
% 7.64/1.50  --bmc1_ucm_max_lemma_size               10
% 7.64/1.50  
% 7.64/1.50  ------ AIG Options
% 7.64/1.50  
% 7.64/1.50  --aig_mode                              false
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation Options
% 7.64/1.50  
% 7.64/1.50  --instantiation_flag                    true
% 7.64/1.50  --inst_sos_flag                         true
% 7.64/1.50  --inst_sos_phase                        true
% 7.64/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.50  --inst_lit_sel_side                     none
% 7.64/1.50  --inst_solver_per_active                1400
% 7.64/1.50  --inst_solver_calls_frac                1.
% 7.64/1.50  --inst_passive_queue_type               priority_queues
% 7.64/1.50  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 7.64/1.50  --inst_passive_queues_freq              [25;2]
% 7.64/1.50  --inst_dismatching                      true
% 7.64/1.50  --inst_eager_unprocessed_to_passive     true
% 7.64/1.50  --inst_prop_sim_given                   true
% 7.64/1.50  --inst_prop_sim_new                     false
% 7.64/1.50  --inst_subs_new                         false
% 7.64/1.50  --inst_eq_res_simp                      false
% 7.64/1.50  --inst_subs_given                       false
% 7.64/1.50  --inst_orphan_elimination               true
% 7.64/1.50  --inst_learning_loop_flag               true
% 7.64/1.50  --inst_learning_start                   3000
% 7.64/1.50  --inst_learning_factor                  2
% 7.64/1.50  --inst_start_prop_sim_after_learn       3
% 7.64/1.50  --inst_sel_renew                        solver
% 7.64/1.50  --inst_lit_activity_flag                true
% 7.64/1.50  --inst_restr_to_given                   false
% 7.64/1.50  --inst_activity_threshold               500
% 7.64/1.50  --inst_out_proof                        true
% 7.64/1.50  
% 7.64/1.50  ------ Resolution Options
% 7.64/1.50  
% 7.64/1.50  --resolution_flag                       false
% 7.64/1.50  --res_lit_sel                           adaptive
% 7.64/1.50  --res_lit_sel_side                      none
% 7.64/1.50  --res_ordering                          kbo
% 7.64/1.50  --res_to_prop_solver                    active
% 7.64/1.50  --res_prop_simpl_new                    false
% 7.64/1.50  --res_prop_simpl_given                  true
% 7.64/1.50  --res_passive_queue_type                priority_queues
% 7.64/1.50  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 7.64/1.50  --res_passive_queues_freq               [15;5]
% 7.64/1.50  --res_forward_subs                      full
% 7.64/1.50  --res_backward_subs                     full
% 7.64/1.50  --res_forward_subs_resolution           true
% 7.64/1.50  --res_backward_subs_resolution          true
% 7.64/1.50  --res_orphan_elimination                true
% 7.64/1.50  --res_time_limit                        2.
% 7.64/1.50  --res_out_proof                         true
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Options
% 7.64/1.50  
% 7.64/1.50  --superposition_flag                    true
% 7.64/1.50  --sup_passive_queue_type                priority_queues
% 7.64/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.50  --demod_completeness_check              fast
% 7.64/1.50  --demod_use_ground                      true
% 7.64/1.50  --sup_to_prop_solver                    passive
% 7.64/1.50  --sup_prop_simpl_new                    true
% 7.64/1.50  --sup_prop_simpl_given                  true
% 7.64/1.50  --sup_fun_splitting                     true
% 7.64/1.50  --sup_smt_interval                      50000
% 7.64/1.50  
% 7.64/1.50  ------ Superposition Simplification Setup
% 7.64/1.50  
% 7.64/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.50  --sup_immed_triv                        [TrivRules]
% 7.64/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_immed_bw_main                     []
% 7.64/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.50  --sup_input_bw                          []
% 7.64/1.50  
% 7.64/1.50  ------ Combination Options
% 7.64/1.50  
% 7.64/1.50  --comb_res_mult                         3
% 7.64/1.50  --comb_sup_mult                         2
% 7.64/1.50  --comb_inst_mult                        10
% 7.64/1.50  
% 7.64/1.50  ------ Debug Options
% 7.64/1.50  
% 7.64/1.50  --dbg_backtrace                         false
% 7.64/1.50  --dbg_dump_prop_clauses                 false
% 7.64/1.50  --dbg_dump_prop_clauses_file            -
% 7.64/1.50  --dbg_out_stat                          false
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ Proving...
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS status Theorem for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  fof(f4,axiom,(
% 7.64/1.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f10,plain,(
% 7.64/1.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 7.64/1.50    inference(ennf_transformation,[],[f4])).
% 7.64/1.50  
% 7.64/1.50  fof(f19,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f10])).
% 7.64/1.50  
% 7.64/1.50  fof(f5,axiom,(
% 7.64/1.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f20,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.64/1.50    inference(cnf_transformation,[],[f5])).
% 7.64/1.50  
% 7.64/1.50  fof(f3,axiom,(
% 7.64/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f18,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f3])).
% 7.64/1.50  
% 7.64/1.50  fof(f6,axiom,(
% 7.64/1.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f21,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f6])).
% 7.64/1.50  
% 7.64/1.50  fof(f2,axiom,(
% 7.64/1.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f9,plain,(
% 7.64/1.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.64/1.50    inference(rectify,[],[f2])).
% 7.64/1.50  
% 7.64/1.50  fof(f17,plain,(
% 7.64/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.64/1.50    inference(cnf_transformation,[],[f9])).
% 7.64/1.50  
% 7.64/1.50  fof(f1,axiom,(
% 7.64/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f12,plain,(
% 7.64/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.64/1.50    inference(nnf_transformation,[],[f1])).
% 7.64/1.50  
% 7.64/1.50  fof(f15,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f12])).
% 7.64/1.50  
% 7.64/1.50  fof(f7,conjecture,(
% 7.64/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.64/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f8,negated_conjecture,(
% 7.64/1.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.64/1.50    inference(negated_conjecture,[],[f7])).
% 7.64/1.50  
% 7.64/1.50  fof(f11,plain,(
% 7.64/1.50    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 7.64/1.50    inference(ennf_transformation,[],[f8])).
% 7.64/1.50  
% 7.64/1.50  fof(f13,plain,(
% 7.64/1.50    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f14,plain,(
% 7.64/1.50    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 7.64/1.50  
% 7.64/1.50  fof(f22,plain,(
% 7.64/1.50    r1_xboole_0(sK0,sK1)),
% 7.64/1.50    inference(cnf_transformation,[],[f14])).
% 7.64/1.50  
% 7.64/1.50  fof(f16,plain,(
% 7.64/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.64/1.50    inference(cnf_transformation,[],[f12])).
% 7.64/1.50  
% 7.64/1.50  fof(f23,plain,(
% 7.64/1.50    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.64/1.50    inference(cnf_transformation,[],[f14])).
% 7.64/1.50  
% 7.64/1.50  cnf(c_4,plain,
% 7.64/1.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f19]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_315,plain,
% 7.64/1.50      ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
% 7.64/1.50      | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_17116,plain,
% 7.64/1.50      ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
% 7.64/1.50      | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_315]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5,plain,
% 7.64/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f20]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7101,plain,
% 7.64/1.50      ( k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_164,plain,
% 7.64/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.64/1.50      theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_454,plain,
% 7.64/1.50      ( ~ r1_tarski(X0,X1)
% 7.64/1.50      | r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
% 7.64/1.50      | k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != X1
% 7.64/1.50      | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != X0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_164]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_717,plain,
% 7.64/1.50      ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
% 7.64/1.50      | ~ r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X1)
% 7.64/1.50      | k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != X1
% 7.64/1.50      | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_454]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3297,plain,
% 7.64/1.50      ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))
% 7.64/1.50      | ~ r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
% 7.64/1.50      | k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k1_xboole_0
% 7.64/1.50      | k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_717]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_359,plain,
% 7.64/1.50      ( ~ r1_tarski(X0,X1)
% 7.64/1.50      | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X2)
% 7.64/1.50      | X2 != X1
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_164]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_698,plain,
% 7.64/1.50      ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),X0)
% 7.64/1.50      | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X1)
% 7.64/1.50      | X1 != X0
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_359]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1343,plain,
% 7.64/1.50      ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1))
% 7.64/1.50      | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0)
% 7.64/1.50      | X0 != k3_xboole_0(sK0,sK1)
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_698]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1345,plain,
% 7.64/1.50      ( ~ r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1))
% 7.64/1.50      | r1_tarski(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
% 7.64/1.50      | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_1343]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3,plain,
% 7.64/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.64/1.50      inference(cnf_transformation,[],[f18]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_984,plain,
% 7.64/1.50      ( r1_tarski(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,sK1)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6,plain,
% 7.64/1.50      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f21]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_345,plain,
% 7.64/1.50      ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_2,plain,
% 7.64/1.50      ( k2_xboole_0(X0,X0) = X0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f17]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_342,plain,
% 7.64/1.50      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_161,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_214,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X0
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 7.64/1.50      | k1_xboole_0 != X0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_161]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_295,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
% 7.64/1.50      | k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_214]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_237,plain,
% 7.64/1.50      ( k3_xboole_0(X0,X1) != X2
% 7.64/1.50      | k1_xboole_0 != X2
% 7.64/1.50      | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_161]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_271,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,sK1) != k1_xboole_0
% 7.64/1.50      | k1_xboole_0 = k3_xboole_0(sK0,sK1)
% 7.64/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_237]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_218,plain,
% 7.64/1.50      ( X0 != X1
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != X1
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = X0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_161]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_229,plain,
% 7.64/1.50      ( X0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = X0
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_218]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_256,plain,
% 7.64/1.50      ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_229]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_254,plain,
% 7.64/1.50      ( k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
% 7.64/1.50      | k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_229]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_160,plain,( X0 = X0 ),theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_246,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_160]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_169,plain,
% 7.64/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_160]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1,plain,
% 7.64/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f15]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_55,plain,
% 7.64/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.64/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_8,negated_conjecture,
% 7.64/1.50      ( r1_xboole_0(sK0,sK1) ),
% 7.64/1.50      inference(cnf_transformation,[],[f22]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_113,plain,
% 7.64/1.50      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_55,c_8]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_114,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_113]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_0,plain,
% 7.64/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.64/1.50      inference(cnf_transformation,[],[f16]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_53,plain,
% 7.64/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.64/1.50      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_7,negated_conjecture,
% 7.64/1.50      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f23]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_108,plain,
% 7.64/1.50      ( k4_xboole_0(sK1,sK2) != X0
% 7.64/1.50      | k3_xboole_0(X1,X0) != k1_xboole_0
% 7.64/1.50      | sK0 != X1 ),
% 7.64/1.50      inference(resolution_lifted,[status(thm)],[c_53,c_7]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_109,plain,
% 7.64/1.50      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 7.64/1.50      inference(unflattening,[status(thm)],[c_108]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(contradiction,plain,
% 7.64/1.50      ( $false ),
% 7.64/1.50      inference(minisat,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_17116,c_7101,c_3297,c_1345,c_984,c_345,c_342,c_295,
% 7.64/1.50                 c_271,c_256,c_254,c_246,c_169,c_114,c_109]) ).
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  ------                               Statistics
% 7.64/1.50  
% 7.64/1.50  ------ General
% 7.64/1.50  
% 7.64/1.50  abstr_ref_over_cycles:                  0
% 7.64/1.50  abstr_ref_under_cycles:                 0
% 7.64/1.50  gc_basic_clause_elim:                   0
% 7.64/1.50  forced_gc_time:                         0
% 7.64/1.50  parsing_time:                           0.008
% 7.64/1.50  unif_index_cands_time:                  0.
% 7.64/1.50  unif_index_add_time:                    0.
% 7.64/1.50  orderings_time:                         0.
% 7.64/1.50  out_proof_time:                         0.008
% 7.64/1.50  total_time:                             0.635
% 7.64/1.50  num_of_symbols:                         40
% 7.64/1.50  num_of_terms:                           28927
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing
% 7.64/1.50  
% 7.64/1.50  num_of_splits:                          0
% 7.64/1.50  num_of_split_atoms:                     0
% 7.64/1.50  num_of_reused_defs:                     0
% 7.64/1.50  num_eq_ax_congr_red:                    7
% 7.64/1.50  num_of_sem_filtered_clauses:            1
% 7.64/1.50  num_of_subtypes:                        0
% 7.64/1.50  monotx_restored_types:                  0
% 7.64/1.50  sat_num_of_epr_types:                   0
% 7.64/1.50  sat_num_of_non_cyclic_types:            0
% 7.64/1.50  sat_guarded_non_collapsed_types:        0
% 7.64/1.50  num_pure_diseq_elim:                    0
% 7.64/1.50  simp_replaced_by:                       0
% 7.64/1.50  res_preprocessed:                       44
% 7.64/1.50  prep_upred:                             0
% 7.64/1.50  prep_unflattend:                        6
% 7.64/1.50  smt_new_axioms:                         0
% 7.64/1.50  pred_elim_cands:                        1
% 7.64/1.50  pred_elim:                              1
% 7.64/1.50  pred_elim_cl:                           1
% 7.64/1.50  pred_elim_cycles:                       4
% 7.64/1.50  merged_defs:                            2
% 7.64/1.50  merged_defs_ncl:                        0
% 7.64/1.50  bin_hyper_res:                          2
% 7.64/1.50  prep_cycles:                            4
% 7.64/1.50  pred_elim_time:                         0.
% 7.64/1.50  splitting_time:                         0.
% 7.64/1.50  sem_filter_time:                        0.
% 7.64/1.50  monotx_time:                            0.001
% 7.64/1.50  subtype_inf_time:                       0.
% 7.64/1.50  
% 7.64/1.50  ------ Problem properties
% 7.64/1.50  
% 7.64/1.50  clauses:                                8
% 7.64/1.50  conjectures:                            0
% 7.64/1.50  epr:                                    0
% 7.64/1.50  horn:                                   8
% 7.64/1.50  ground:                                 3
% 7.64/1.50  unary:                                  7
% 7.64/1.50  binary:                                 1
% 7.64/1.50  lits:                                   9
% 7.64/1.50  lits_eq:                                7
% 7.64/1.50  fd_pure:                                0
% 7.64/1.50  fd_pseudo:                              0
% 7.64/1.50  fd_cond:                                1
% 7.64/1.50  fd_pseudo_cond:                         0
% 7.64/1.50  ac_symbols:                             0
% 7.64/1.50  
% 7.64/1.50  ------ Propositional Solver
% 7.64/1.50  
% 7.64/1.50  prop_solver_calls:                      34
% 7.64/1.50  prop_fast_solver_calls:                 330
% 7.64/1.50  smt_solver_calls:                       0
% 7.64/1.50  smt_fast_solver_calls:                  0
% 7.64/1.50  prop_num_of_clauses:                    6126
% 7.64/1.50  prop_preprocess_simplified:             7189
% 7.64/1.50  prop_fo_subsumed:                       0
% 7.64/1.50  prop_solver_time:                       0.
% 7.64/1.50  smt_solver_time:                        0.
% 7.64/1.50  smt_fast_solver_time:                   0.
% 7.64/1.50  prop_fast_solver_time:                  0.
% 7.64/1.50  prop_unsat_core_time:                   0.
% 7.64/1.50  
% 7.64/1.50  ------ QBF
% 7.64/1.50  
% 7.64/1.50  qbf_q_res:                              0
% 7.64/1.50  qbf_num_tautologies:                    0
% 7.64/1.50  qbf_prep_cycles:                        0
% 7.64/1.50  
% 7.64/1.50  ------ BMC1
% 7.64/1.50  
% 7.64/1.50  bmc1_current_bound:                     -1
% 7.64/1.50  bmc1_last_solved_bound:                 -1
% 7.64/1.50  bmc1_unsat_core_size:                   -1
% 7.64/1.50  bmc1_unsat_core_parents_size:           -1
% 7.64/1.50  bmc1_merge_next_fun:                    0
% 7.64/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.64/1.50  
% 7.64/1.50  ------ Instantiation
% 7.64/1.50  
% 7.64/1.50  inst_num_of_clauses:                    1458
% 7.64/1.50  inst_num_in_passive:                    742
% 7.64/1.50  inst_num_in_active:                     631
% 7.64/1.50  inst_num_in_unprocessed:                84
% 7.64/1.50  inst_num_of_loops:                      724
% 7.64/1.50  inst_num_of_learning_restarts:          0
% 7.64/1.50  inst_num_moves_active_passive:          86
% 7.64/1.50  inst_lit_activity:                      0
% 7.64/1.50  inst_lit_activity_moves:                0
% 7.64/1.50  inst_num_tautologies:                   0
% 7.64/1.50  inst_num_prop_implied:                  0
% 7.64/1.50  inst_num_existing_simplified:           0
% 7.64/1.50  inst_num_eq_res_simplified:             0
% 7.64/1.50  inst_num_child_elim:                    0
% 7.64/1.50  inst_num_of_dismatching_blockings:      566
% 7.64/1.50  inst_num_of_non_proper_insts:           1676
% 7.64/1.50  inst_num_of_duplicates:                 0
% 7.64/1.50  inst_inst_num_from_inst_to_res:         0
% 7.64/1.50  inst_dismatching_checking_time:         0.
% 7.64/1.50  
% 7.64/1.50  ------ Resolution
% 7.64/1.50  
% 7.64/1.50  res_num_of_clauses:                     0
% 7.64/1.50  res_num_in_passive:                     0
% 7.64/1.50  res_num_in_active:                      0
% 7.64/1.50  res_num_of_loops:                       48
% 7.64/1.50  res_forward_subset_subsumed:            258
% 7.64/1.50  res_backward_subset_subsumed:           4
% 7.64/1.50  res_forward_subsumed:                   0
% 7.64/1.50  res_backward_subsumed:                  0
% 7.64/1.50  res_forward_subsumption_resolution:     0
% 7.64/1.50  res_backward_subsumption_resolution:    0
% 7.64/1.50  res_clause_to_clause_subsumption:       2770
% 7.64/1.50  res_orphan_elimination:                 0
% 7.64/1.50  res_tautology_del:                      209
% 7.64/1.50  res_num_eq_res_simplified:              1
% 7.64/1.50  res_num_sel_changes:                    0
% 7.64/1.50  res_moves_from_active_to_pass:          0
% 7.64/1.50  
% 7.64/1.50  ------ Superposition
% 7.64/1.50  
% 7.64/1.50  sup_time_total:                         0.
% 7.64/1.50  sup_time_generating:                    0.
% 7.64/1.50  sup_time_sim_full:                      0.
% 7.64/1.50  sup_time_sim_immed:                     0.
% 7.64/1.50  
% 7.64/1.50  sup_num_of_clauses:                     1498
% 7.64/1.50  sup_num_in_active:                      122
% 7.64/1.50  sup_num_in_passive:                     1376
% 7.64/1.50  sup_num_of_loops:                       144
% 7.64/1.50  sup_fw_superposition:                   2473
% 7.64/1.50  sup_bw_superposition:                   2318
% 7.64/1.50  sup_immediate_simplified:               2371
% 7.64/1.50  sup_given_eliminated:                   1
% 7.64/1.50  comparisons_done:                       0
% 7.64/1.50  comparisons_avoided:                    0
% 7.64/1.50  
% 7.64/1.50  ------ Simplifications
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  sim_fw_subset_subsumed:                 0
% 7.64/1.50  sim_bw_subset_subsumed:                 0
% 7.64/1.50  sim_fw_subsumed:                        207
% 7.64/1.50  sim_bw_subsumed:                        6
% 7.64/1.50  sim_fw_subsumption_res:                 0
% 7.64/1.50  sim_bw_subsumption_res:                 0
% 7.64/1.50  sim_tautology_del:                      0
% 7.64/1.50  sim_eq_tautology_del:                   1024
% 7.64/1.50  sim_eq_res_simp:                        0
% 7.64/1.50  sim_fw_demodulated:                     1969
% 7.64/1.50  sim_bw_demodulated:                     126
% 7.64/1.50  sim_light_normalised:                   944
% 7.64/1.50  sim_joinable_taut:                      0
% 7.64/1.50  sim_joinable_simp:                      0
% 7.64/1.50  sim_ac_normalised:                      0
% 7.64/1.50  sim_smt_subsumption:                    0
% 7.64/1.50  
%------------------------------------------------------------------------------
