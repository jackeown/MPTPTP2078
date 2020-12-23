%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0083+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:19 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   33 (  57 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  92 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f273,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f394,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f437,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f273,f394,f394])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f379,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f120,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f121,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f120])).

fof(f209,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f121])).

fof(f268,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK17,sK15),k3_xboole_0(sK17,sK16))
      & r1_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f269,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK17,sK15),k3_xboole_0(sK17,sK16))
    & r1_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f209,f268])).

fof(f430,plain,(
    r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f269])).

fof(f106,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f190,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f191,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f190])).

fof(f413,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f191])).

fof(f431,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK17,sK15),k3_xboole_0(sK17,sK16)) ),
    inference(cnf_transformation,[],[f269])).

fof(f510,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK17,k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,k4_xboole_0(sK17,sK16))) ),
    inference(definition_unfolding,[],[f431,f394,f394])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f437])).

cnf(c_107,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f379])).

cnf(c_4834,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_107])).

cnf(c_6076,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4834])).

cnf(c_158,negated_conjecture,
    ( r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f430])).

cnf(c_4806,plain,
    ( r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_140,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f413])).

cnf(c_4822,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X3) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_41849,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,sK16) != iProver_top
    | r1_tarski(X0,sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_4806,c_4822])).

cnf(c_43455,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK15)),X1) = iProver_top
    | r1_tarski(X1,sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_6076,c_41849])).

cnf(c_157,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK17,k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,k4_xboole_0(sK17,sK16))) ),
    inference(cnf_transformation,[],[f510])).

cnf(c_4807,plain,
    ( r1_xboole_0(k4_xboole_0(sK17,k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,k4_xboole_0(sK17,sK16))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_44137,plain,
    ( r1_tarski(k4_xboole_0(sK17,k4_xboole_0(sK17,sK16)),sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_43455,c_4807])).

cnf(c_44238,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44137,c_6076])).

%------------------------------------------------------------------------------
