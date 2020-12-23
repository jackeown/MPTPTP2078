%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0061+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f288,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f338,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f381,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f288,f338])).

fof(f94,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f94])).

fof(f157,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f95])).

fof(f215,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) != k4_xboole_0(X0,k3_xboole_0(X1,X2))
   => k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k3_xboole_0(sK16,sK17)) ),
    introduced(choice_axiom,[])).

fof(f216,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k3_xboole_0(sK16,sK17)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f157,f215])).

fof(f346,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k3_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f216])).

fof(f417,plain,(
    k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) ),
    inference(definition_unfolding,[],[f346,f338])).

cnf(c_2077,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6878,plain,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) = k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_69,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f381])).

cnf(c_5566,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) = k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_2078,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4704,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) != X0
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != X0
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) = k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_5565,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) != k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) = k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17)))
    | k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_4704])).

cnf(c_126,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK16,k4_xboole_0(sK16,sK17))) ),
    inference(cnf_transformation,[],[f417])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6878,c_5566,c_5565,c_126])).

%------------------------------------------------------------------------------
