%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0077+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of clauses        :   38 (  56 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  286 ( 587 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f136])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f124])).

fof(f237,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f134,f237])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f238])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f182,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f183,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f182])).

fof(f397,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f83,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f375,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f364,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f130,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f298,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f114,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f115,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f114])).

fof(f194,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f115])).

fof(f253,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
        & ( ~ r1_xboole_0(sK15,sK17)
          | ~ r1_xboole_0(sK15,sK16) ) )
      | ( r1_xboole_0(sK15,sK17)
        & r1_xboole_0(sK15,sK16)
        & ~ r1_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ) ) ),
    introduced(choice_axiom,[])).

fof(f254,plain,
    ( ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
      & ( ~ r1_xboole_0(sK15,sK17)
        | ~ r1_xboole_0(sK15,sK16) ) )
    | ( r1_xboole_0(sK15,sK17)
      & r1_xboole_0(sK15,sK16)
      & ~ r1_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f194,f253])).

fof(f412,plain,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f254])).

fof(f117,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f414,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f117])).

fof(f411,plain,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f254])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f208,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f209,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f208])).

fof(f210,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f209])).

fof(f211,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f212,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f210,f211])).

fof(f266,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f212])).

fof(f491,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f266])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f382,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f257,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f309,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f238])).

fof(f310,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f238])).

fof(f407,plain,
    ( ~ r1_xboole_0(sK15,sK17)
    | ~ r1_xboole_0(sK15,sK16)
    | ~ r1_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f254])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f317])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f311])).

cnf(c_721,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57,c_52])).

cnf(c_722,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_7098,plain,
    ( ~ r1_xboole_0(sK15,X0)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),X0)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK15) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_10819,plain,
    ( ~ r1_xboole_0(sK15,sK16)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK16)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK15) ),
    inference(instantiation,[status(thm)],[c_7098])).

cnf(c_7092,plain,
    ( ~ r1_xboole_0(X0,sK15)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),X0)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK15) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_9743,plain,
    ( ~ r1_xboole_0(sK17,sK15)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK17)
    | ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK15) ),
    inference(instantiation,[status(thm)],[c_7092])).

cnf(c_139,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f397])).

cnf(c_118,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f375])).

cnf(c_107,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f364])).

cnf(c_6586,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_118,c_107])).

cnf(c_6746,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_139,c_6586])).

cnf(c_41,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f298])).

cnf(c_149,negated_conjecture,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f412])).

cnf(c_5077,plain,
    ( r1_xboole_0(k2_xboole_0(sK16,sK17),sK15)
    | r1_xboole_0(sK15,sK17) ),
    inference(resolution,[status(thm)],[c_41,c_149])).

cnf(c_8466,plain,
    ( r1_xboole_0(sK17,sK15)
    | r1_xboole_0(sK15,sK17) ),
    inference(resolution,[status(thm)],[c_6746,c_5077])).

cnf(c_7179,plain,
    ( ~ r1_xboole_0(sK17,sK15)
    | r1_xboole_0(sK15,sK17) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_8469,plain,
    ( r1_xboole_0(sK15,sK17) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8466,c_7179])).

cnf(c_8483,plain,
    ( r1_xboole_0(sK17,sK15) ),
    inference(resolution,[status(thm)],[c_8469,c_41])).

cnf(c_156,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f414])).

cnf(c_6740,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_139,c_156])).

cnf(c_150,negated_conjecture,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f411])).

cnf(c_5078,plain,
    ( r1_xboole_0(k2_xboole_0(sK16,sK17),sK15)
    | r1_xboole_0(sK15,sK16) ),
    inference(resolution,[status(thm)],[c_41,c_150])).

cnf(c_6942,plain,
    ( r1_xboole_0(sK16,sK15)
    | r1_xboole_0(sK15,sK16) ),
    inference(resolution,[status(thm)],[c_6740,c_5078])).

cnf(c_5051,plain,
    ( ~ r1_xboole_0(sK16,sK15)
    | r1_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_7517,plain,
    ( r1_xboole_0(sK15,sK16) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6942,c_5051])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f491])).

cnf(c_124,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f382])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f257])).

cnf(c_2430,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_124,c_2])).

cnf(c_7176,plain,
    ( ~ r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),k2_xboole_0(sK16,sK17))
    | r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK17)
    | r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK16) ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_54,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X0) ),
    inference(cnf_transformation,[],[f309])).

cnf(c_6618,plain,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),sK15) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_53,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X1) ),
    inference(cnf_transformation,[],[f310])).

cnf(c_6619,plain,
    ( r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | r2_hidden(sK9(sK15,k2_xboole_0(sK16,sK17)),k2_xboole_0(sK16,sK17)) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_154,negated_conjecture,
    ( ~ r1_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    | ~ r1_xboole_0(sK15,sK17)
    | ~ r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f407])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10819,c_9743,c_8483,c_8469,c_7517,c_7176,c_6618,c_6619,c_154])).

%------------------------------------------------------------------------------
