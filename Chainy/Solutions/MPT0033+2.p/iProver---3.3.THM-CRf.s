%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0033+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:13 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of clauses        :   24 (  26 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 114 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f106])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f247,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f172,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f104])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f58,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f58])).

fof(f110,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f167,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17))
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f168,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17))
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f110,f167])).

fof(f261,plain,(
    ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f168])).

fof(f46,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f246,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f265,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f260,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_80,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f251])).

cnf(c_4386,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),X0)
    | r1_tarski(k3_xboole_0(sK15,sK17),X1) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_7160,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),X0)
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK15)
    | ~ r1_tarski(sK15,X0) ),
    inference(instantiation,[status(thm)],[c_4386])).

cnf(c_14904,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),sK16)
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK15)
    | ~ r1_tarski(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_7160])).

cnf(c_1701,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4282,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(sK15,sK17),sK17)
    | k3_xboole_0(sK15,sK17) != X0
    | sK17 != X1 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_6767,plain,
    ( ~ r1_tarski(X0,sK17)
    | r1_tarski(k3_xboole_0(sK15,sK17),sK17)
    | k3_xboole_0(sK15,sK17) != X0
    | sK17 != sK17 ),
    inference(instantiation,[status(thm)],[c_4282])).

cnf(c_14681,plain,
    ( ~ r1_tarski(k3_xboole_0(sK17,sK15),sK17)
    | r1_tarski(k3_xboole_0(sK15,sK17),sK17)
    | k3_xboole_0(sK15,sK17) != k3_xboole_0(sK17,sK15)
    | sK17 != sK17 ),
    inference(instantiation,[status(thm)],[c_6767])).

cnf(c_1695,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6768,plain,
    ( sK17 = sK17 ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f247])).

cnf(c_5549,plain,
    ( r1_tarski(k3_xboole_0(sK17,sK15),sK17) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_4408,plain,
    ( k3_xboole_0(sK15,sK17) = k3_xboole_0(sK17,sK15) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4371,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f249])).

cnf(c_3967,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK17,sK16))
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK16)
    | ~ r1_tarski(k3_xboole_0(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_89,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f261])).

cnf(c_75,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f246])).

cnf(c_94,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f265])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_1685,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK17),k3_xboole_0(sK17,sK16)) ),
    inference(theory_normalisation,[status(thm)],[c_89,c_75,c_3,c_94,c_2])).

cnf(c_90,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f260])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14904,c_14681,c_6768,c_5549,c_4408,c_4371,c_3967,c_1685,c_90])).

%------------------------------------------------------------------------------
