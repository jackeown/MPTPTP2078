%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0263+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:52 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 (  66 expanded)
%              Number of equality atoms :   31 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f15,plain,(
    k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_74,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,negated_conjecture,
    ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_73,negated_conjecture,
    ( k3_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_133,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK0)) != k1_tarski(sK0) ),
    inference(demodulation,[status(thm)],[c_74,c_73])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_42,plain,
    ( r2_hidden(X0,X1)
    | k1_tarski(X0) != k1_tarski(sK0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_43,plain,
    ( r2_hidden(X0,sK1)
    | k1_tarski(X0) != k1_tarski(sK0) ),
    inference(unflattening,[status(thm)],[c_42])).

cnf(c_57,plain,
    ( X0 != X1
    | k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | k1_tarski(X0) != k1_tarski(sK0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_43])).

cnf(c_58,plain,
    ( k3_xboole_0(sK1,k1_tarski(X0)) = k1_tarski(X0)
    | k1_tarski(X0) != k1_tarski(sK0) ),
    inference(unflattening,[status(thm)],[c_57])).

cnf(c_72,plain,
    ( k3_xboole_0(sK1,k1_tarski(X0_35)) = k1_tarski(X0_35)
    | k1_tarski(X0_35) != k1_tarski(sK0) ),
    inference(subtyping,[status(esa)],[c_58])).

cnf(c_101,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK0)) = k1_tarski(sK0) ),
    inference(equality_resolution,[status(thm)],[c_72])).

cnf(c_134,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(light_normalisation,[status(thm)],[c_133,c_101])).

cnf(c_135,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_134])).


%------------------------------------------------------------------------------
