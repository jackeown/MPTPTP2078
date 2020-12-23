%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0084+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:26 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 115 expanded)
%              Number of equality atoms :   35 (  38 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f18,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_90,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_91,plain,
    ( k3_xboole_0(sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_90])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_129,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_91,c_3])).

cnf(c_132,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_129])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_51,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_5,negated_conjecture,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_97,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | k3_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_5])).

cnf(c_98,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_165,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_132,c_98])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_49,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_102,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_49,c_7])).

cnf(c_103,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_241,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_165,c_103])).

cnf(c_242,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_241])).


%------------------------------------------------------------------------------
