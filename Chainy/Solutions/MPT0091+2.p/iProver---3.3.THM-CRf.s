%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   34 (  69 expanded)
%              Number of clauses        :   18 (  27 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 149 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f397,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f130,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f131,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f130])).

fof(f223,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f131])).

fof(f282,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17))
      & r1_xboole_0(sK15,sK17)
      & ~ r1_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f283,plain,
    ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17))
    & r1_xboole_0(sK15,sK17)
    & ~ r1_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f223,f282])).

fof(f456,plain,(
    r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f283])).

fof(f129,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f281,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f129])).

fof(f453,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f80,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f401,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f80])).

fof(f457,plain,(
    r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f283])).

fof(f454,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f281])).

fof(f455,plain,(
    ~ r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f283])).

cnf(c_111,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f397])).

cnf(c_169,negated_conjecture,
    ( r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f456])).

cnf(c_5204,plain,
    ( r1_xboole_0(sK15,sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_167,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f453])).

cnf(c_5206,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_6388,plain,
    ( k4_xboole_0(sK15,sK17) = sK15 ),
    inference(superposition,[status(thm)],[c_5204,c_5206])).

cnf(c_115,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f401])).

cnf(c_7991,plain,
    ( k4_xboole_0(sK15,k2_xboole_0(sK17,X0)) = k4_xboole_0(sK15,X0) ),
    inference(superposition,[status(thm)],[c_6388,c_115])).

cnf(c_8473,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(X0,sK17)) = k4_xboole_0(sK15,k2_xboole_0(sK17,X0)) ),
    inference(superposition,[status(thm)],[c_111,c_7991])).

cnf(c_8496,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(X0,sK17)) = k4_xboole_0(sK15,X0) ),
    inference(light_normalisation,[status(thm)],[c_8473,c_7991])).

cnf(c_168,negated_conjecture,
    ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f457])).

cnf(c_5205,plain,
    ( r1_xboole_0(sK15,k4_xboole_0(sK16,sK17)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_6387,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK16,sK17)) = sK15 ),
    inference(superposition,[status(thm)],[c_5205,c_5206])).

cnf(c_10513,plain,
    ( k4_xboole_0(sK15,sK16) = sK15 ),
    inference(superposition,[status(thm)],[c_8496,c_6387])).

cnf(c_166,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f454])).

cnf(c_6262,plain,
    ( r1_xboole_0(sK15,sK16)
    | k4_xboole_0(sK15,sK16) != sK15 ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_170,negated_conjecture,
    ( ~ r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f455])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10513,c_6262,c_170])).

%------------------------------------------------------------------------------
