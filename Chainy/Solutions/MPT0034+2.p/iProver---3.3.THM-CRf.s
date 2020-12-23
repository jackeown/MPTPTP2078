%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:13 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :   63 (  88 expanded)
%              Number of clauses        :   33 (  35 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 193 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f59])).

fof(f112,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f113,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f112])).

fof(f170,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18))
      & r1_tarski(sK17,sK18)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f171,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18))
    & r1_tarski(sK17,sK18)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f113,f170])).

fof(f265,plain,(
    r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f171])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f243,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f53,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f258,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f46,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f249,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f175,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f250,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f105])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f266,plain,(
    ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18)) ),
    inference(cnf_transformation,[],[f171])).

fof(f264,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f171])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_91,negated_conjecture,
    ( r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f265])).

cnf(c_3250,plain,
    ( r1_tarski(sK17,sK18) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91])).

cnf(c_69,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f243])).

cnf(c_3264,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_70176,plain,
    ( k2_xboole_0(sK17,sK18) = sK18 ),
    inference(superposition,[status(thm)],[c_3250,c_3264])).

cnf(c_84,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f258])).

cnf(c_75,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f249])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f250])).

cnf(c_3259,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_4319,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3259])).

cnf(c_5640,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_75,c_4319])).

cnf(c_9731,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_84,c_5640])).

cnf(c_72338,plain,
    ( r1_tarski(k3_xboole_0(X0,sK17),sK18) = iProver_top ),
    inference(superposition,[status(thm)],[c_70176,c_9731])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f252])).

cnf(c_3257,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_90,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18)) ),
    inference(cnf_transformation,[],[f266])).

cnf(c_3251,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_41270,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),sK18) != iProver_top
    | r1_tarski(k3_xboole_0(sK15,sK17),sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_3251])).

cnf(c_92,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f264])).

cnf(c_105,plain,
    ( r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_107,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_3934,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18))
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK18)
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_3935,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK18)) = iProver_top
    | r1_tarski(k3_xboole_0(sK15,sK17),sK18) != iProver_top
    | r1_tarski(k3_xboole_0(sK15,sK17),sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_77,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f251])).

cnf(c_4563,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,X0))
    | r1_tarski(k3_xboole_0(sK15,sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_6417,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17))
    | r1_tarski(k3_xboole_0(sK15,sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_4563])).

cnf(c_6419,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17)) != iProver_top
    | r1_tarski(k3_xboole_0(sK15,sK17),sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6417])).

cnf(c_89,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f263])).

cnf(c_6418,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17))
    | ~ r1_tarski(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_6421,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17)) = iProver_top
    | r1_tarski(sK15,sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6418])).

cnf(c_43245,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),sK18) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41270,c_105,c_107,c_3935,c_6419,c_6421])).

cnf(c_75032,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_72338,c_43245])).

%------------------------------------------------------------------------------
