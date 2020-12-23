%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0200+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:42 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   21 (  29 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   22 (  30 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_8,plain,
    ( k2_enumset1(X0_34,X1_34,X2_34,X3_34) = k2_enumset1(X3_34,X2_34,X0_34,X1_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_15,plain,
    ( k2_enumset1(X0_34,X1_34,X2_34,X3_34) = k2_enumset1(X1_34,X0_34,X3_34,X2_34) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_0,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_9,plain,
    ( k2_enumset1(X0_34,X1_34,X2_34,X3_34) = k2_enumset1(X1_34,X0_34,X2_34,X3_34) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_42,plain,
    ( k2_enumset1(X0_34,X1_34,X2_34,X3_34) = k2_enumset1(X0_34,X1_34,X3_34,X2_34) ),
    inference(superposition,[status(thm)],[c_15,c_9])).

cnf(c_2,negated_conjecture,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_7,negated_conjecture,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_14,plain,
    ( k2_enumset1(sK0,sK1,sK3,sK2) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_8,c_7])).

cnf(c_139,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_42,c_14])).

cnf(c_188,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_139])).


%------------------------------------------------------------------------------
