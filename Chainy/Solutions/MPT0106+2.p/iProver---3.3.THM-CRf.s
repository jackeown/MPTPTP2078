%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0106+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:21 EST 2020

% Result     : Theorem 54.68s
% Output     : CNFRefutation 54.68s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 129 expanded)
%              Number of clauses        :   17 (  29 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 ( 130 expanded)
%              Number of equality atoms :   45 ( 129 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f386,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f145,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f496,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f145])).

fof(f503,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f496,f436])).

fof(f89,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f436,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

fof(f538,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f386,f503,f436])).

fof(f142,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f493,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f142])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f314,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f98,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f445,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f98])).

fof(f590,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f445,f503,f503,f436])).

fof(f83,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f430,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f83])).

fof(f576,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(definition_unfolding,[],[f430,f503,f503])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f429,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f82])).

fof(f575,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f429,f503])).

fof(f150,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f151,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f150])).

fof(f252,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) != k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f151])).

fof(f308,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) != k4_xboole_0(k5_xboole_0(X0,X1),X2)
   => k2_xboole_0(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(sK16,k2_xboole_0(sK15,sK17))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    introduced(choice_axiom,[])).

fof(f309,plain,(
    k2_xboole_0(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(sK16,k2_xboole_0(sK15,sK17))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f252,f308])).

fof(f501,plain,(
    k2_xboole_0(k4_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k4_xboole_0(sK16,k2_xboole_0(sK15,sK17))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f309])).

fof(f622,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,k5_xboole_0(k5_xboole_0(sK15,sK17),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,k5_xboole_0(k5_xboole_0(sK15,sK17),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(definition_unfolding,[],[f501,f503,f503,f503])).

cnf(c_75,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f538])).

cnf(c_181,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f493])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f314])).

cnf(c_2973,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_75,c_181,c_5])).

cnf(c_133,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f590])).

cnf(c_2943,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_133,c_181,c_5])).

cnf(c_119,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1) ),
    inference(cnf_transformation,[],[f576])).

cnf(c_2952,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X1) ),
    inference(theory_normalisation,[status(thm)],[c_119,c_181,c_5])).

cnf(c_118,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f575])).

cnf(c_2953,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_118,c_181,c_5])).

cnf(c_188,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,k5_xboole_0(k5_xboole_0(sK15,sK17),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(k5_xboole_0(sK16,sK17),k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))),k4_xboole_0(sK16,k5_xboole_0(k5_xboole_0(sK15,sK17),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(cnf_transformation,[],[f622])).

cnf(c_2926,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(sK15,k5_xboole_0(sK16,k5_xboole_0(sK17,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))))),k5_xboole_0(k4_xboole_0(sK16,k5_xboole_0(sK15,k5_xboole_0(sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(sK16,k5_xboole_0(sK17,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))))),k4_xboole_0(k4_xboole_0(sK15,k5_xboole_0(sK16,k5_xboole_0(sK17,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))))),k4_xboole_0(sK16,k5_xboole_0(sK15,k5_xboole_0(sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))))))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(theory_normalisation,[status(thm)],[c_188,c_181,c_5])).

cnf(c_23977,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k5_xboole_0(k4_xboole_0(sK16,k5_xboole_0(sK15,k5_xboole_0(sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k4_xboole_0(sK16,k5_xboole_0(sK15,k5_xboole_0(sK17,k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))))))))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(superposition,[status(thm)],[c_2953,c_2926])).

cnf(c_30682,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k5_xboole_0(k4_xboole_0(k4_xboole_0(sK16,sK15),sK17),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK15,sK16),sK17),k4_xboole_0(k4_xboole_0(sK16,sK15),sK17))))) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(superposition,[status(thm)],[c_2953,c_23977])).

cnf(c_35500,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(sK15,sK16),k5_xboole_0(k4_xboole_0(sK16,sK15),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15))))),sK17) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(superposition,[status(thm)],[c_2952,c_30682])).

cnf(c_39008,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(sK15,k5_xboole_0(sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),sK17) != k4_xboole_0(k5_xboole_0(sK15,sK16),sK17) ),
    inference(superposition,[status(thm)],[c_2943,c_35500])).

cnf(c_171227,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2973,c_39008])).

%------------------------------------------------------------------------------
