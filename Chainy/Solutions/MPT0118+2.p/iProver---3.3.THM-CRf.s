%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0118+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   33 (  64 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  87 expanded)
%              Number of equality atoms :   53 (  86 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f343,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f105,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f489,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f105])).

fof(f560,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f343,f489,f489])).

fof(f109,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f493,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f109])).

fof(f648,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f493,f489,f489,f489])).

fof(f60,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f60])).

fof(f200,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f61])).

fof(f332,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k4_xboole_0(sK13,sK15),sK14) != k4_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK15,sK14)) ),
    introduced(choice_axiom,[])).

fof(f333,plain,(
    k3_xboole_0(k4_xboole_0(sK13,sK15),sK14) != k4_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK15,sK14)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f200,f332])).

fof(f440,plain,(
    k3_xboole_0(k4_xboole_0(sK13,sK15),sK14) != k4_xboole_0(k3_xboole_0(sK13,sK14),k3_xboole_0(sK15,sK14)) ),
    inference(cnf_transformation,[],[f333])).

fof(f602,plain,(
    k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) ),
    inference(definition_unfolding,[],[f440,f489,f489,f489])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f560])).

cnf(c_23486,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,sK14)) = k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2712,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_20861,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) = k4_xboole_0(X0,X1)
    | k4_xboole_0(sK15,k4_xboole_0(sK15,sK14)) != X1
    | k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)) != X0 ),
    inference(instantiation,[status(thm)],[c_2712])).

cnf(c_21839,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) = k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),X0)
    | k4_xboole_0(sK15,k4_xboole_0(sK15,sK14)) != X0
    | k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)) != k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)) ),
    inference(instantiation,[status(thm)],[c_20861])).

cnf(c_22427,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) = k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))
    | k4_xboole_0(sK15,k4_xboole_0(sK15,sK14)) != k4_xboole_0(sK14,k4_xboole_0(sK14,sK15))
    | k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)) != k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)) ),
    inference(instantiation,[status(thm)],[c_21839])).

cnf(c_22148,plain,
    ( k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)) = k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2710,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8634,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) != X0
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != X0
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) ),
    inference(instantiation,[status(thm)],[c_2710])).

cnf(c_9371,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) != k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) ),
    inference(instantiation,[status(thm)],[c_8634])).

cnf(c_151,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f648])).

cnf(c_8904,plain,
    ( k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15))) = k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15))) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_8636,plain,
    ( X0 != X1
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != X1
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = X0 ),
    inference(instantiation,[status(thm)],[c_2710])).

cnf(c_8640,plain,
    ( X0 != k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15)))
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = X0
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15))) ),
    inference(instantiation,[status(thm)],[c_8636])).

cnf(c_8666,plain,
    ( k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15))) != k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15)))
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = k4_xboole_0(k4_xboole_0(sK14,k4_xboole_0(sK14,sK13)),k4_xboole_0(sK14,k4_xboole_0(sK14,sK15)))
    | k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15))) ),
    inference(instantiation,[status(thm)],[c_8640])).

cnf(c_8611,plain,
    ( k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) = k4_xboole_0(sK14,k4_xboole_0(sK14,k4_xboole_0(sK13,sK15))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_99,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(sK13,sK15),k4_xboole_0(k4_xboole_0(sK13,sK15),sK14)) != k4_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK14))) ),
    inference(cnf_transformation,[],[f602])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23486,c_22427,c_22148,c_9371,c_8904,c_8666,c_8611,c_99])).

%------------------------------------------------------------------------------
