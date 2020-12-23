%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0078+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 19.76s
% Output     : CNFRefutation 19.76s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 191 expanded)
%              Number of clauses        :   56 (  67 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  361 ( 712 expanded)
%              Number of equality atoms :   94 ( 186 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f129])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f207])).

fof(f209,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f208,f209])).

fof(f266,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f210])).

fof(f115,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f116,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f115])).

fof(f196,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f116])).

fof(f197,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f196])).

fof(f256,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK15 != sK17
      & r1_xboole_0(sK17,sK16)
      & r1_xboole_0(sK15,sK16)
      & k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f257,plain,
    ( sK15 != sK17
    & r1_xboole_0(sK17,sK16)
    & r1_xboole_0(sK15,sK16)
    & k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f197,f256])).

fof(f413,plain,(
    k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK16) ),
    inference(cnf_transformation,[],[f257])).

fof(f113,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f409,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f118,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f418,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f118])).

fof(f82,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f377,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f79,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f374,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f79])).

fof(f92,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f387,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f382,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f481,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f387,f382])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f385,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f260,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f221,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f222,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f221])).

fof(f223,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f222])).

fof(f224,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f225,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f223,f224])).

fof(f283,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f225])).

fof(f499,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f283])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f137,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f137])).

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

fof(f125,plain,(
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

fof(f135,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f125])).

fof(f240,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f135,f240])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f241])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f133,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f234,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f133])).

fof(f235,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f236,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f234,f235])).

fof(f307,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f306,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f416,plain,(
    sK15 != sK17 ),
    inference(cnf_transformation,[],[f257])).

fof(f415,plain,(
    r1_xboole_0(sK17,sK16) ),
    inference(cnf_transformation,[],[f257])).

fof(f414,plain,(
    r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f257])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f266])).

cnf(c_5242,plain,
    ( ~ r1_tarski(X0,sK17)
    | ~ r2_hidden(sK7(sK15,sK17),X0)
    | r2_hidden(sK7(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_78179,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,sK16),sK17)
    | ~ r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK7(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_5242])).

cnf(c_78194,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK17) != iProver_top
    | r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK15,sK16)) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78179])).

cnf(c_7186,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK7(sK15,sK17),X0)
    | r2_hidden(sK7(sK15,sK17),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_28882,plain,
    ( ~ r1_tarski(k4_xboole_0(sK17,sK15),X0)
    | r2_hidden(sK7(sK15,sK17),X0)
    | ~ r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK17,sK15)) ),
    inference(instantiation,[status(thm)],[c_7186])).

cnf(c_60735,plain,
    ( ~ r1_tarski(k4_xboole_0(sK17,sK15),sK16)
    | ~ r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK17,sK15))
    | r2_hidden(sK7(sK15,sK17),sK16) ),
    inference(instantiation,[status(thm)],[c_28882])).

cnf(c_60747,plain,
    ( r1_tarski(k4_xboole_0(sK17,sK15),sK16) != iProver_top
    | r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK17,sK15)) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60735])).

cnf(c_155,negated_conjecture,
    ( k2_xboole_0(sK15,sK16) = k2_xboole_0(sK17,sK16) ),
    inference(cnf_transformation,[],[f413])).

cnf(c_148,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f409])).

cnf(c_8086,plain,
    ( k2_xboole_0(sK17,k2_xboole_0(sK15,sK16)) = k2_xboole_0(sK17,sK16) ),
    inference(superposition,[status(thm)],[c_155,c_148])).

cnf(c_8094,plain,
    ( k2_xboole_0(sK17,k2_xboole_0(sK15,sK16)) = k2_xboole_0(sK15,sK16) ),
    inference(light_normalisation,[status(thm)],[c_8086,c_155])).

cnf(c_157,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f418])).

cnf(c_4506,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_13627,plain,
    ( r1_tarski(sK17,k2_xboole_0(sK15,sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8094,c_4506])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f377])).

cnf(c_4527,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_27458,plain,
    ( r1_tarski(k4_xboole_0(sK17,sK15),sK16) = iProver_top ),
    inference(superposition,[status(thm)],[c_13627,c_4527])).

cnf(c_114,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f374])).

cnf(c_8062,plain,
    ( k4_xboole_0(k2_xboole_0(sK15,sK16),sK16) = k4_xboole_0(sK17,sK16) ),
    inference(superposition,[status(thm)],[c_155,c_114])).

cnf(c_8075,plain,
    ( k4_xboole_0(sK15,sK16) = k4_xboole_0(sK17,sK16) ),
    inference(demodulation,[status(thm)],[c_8062,c_114])).

cnf(c_126,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f481])).

cnf(c_124,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f385])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f260])).

cnf(c_2448,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_126,c_124,c_2])).

cnf(c_8329,plain,
    ( k2_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK17,k4_xboole_0(sK15,sK16))) = sK17 ),
    inference(superposition,[status(thm)],[c_8075,c_2448])).

cnf(c_13631,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),sK17) = iProver_top ),
    inference(superposition,[status(thm)],[c_8329,c_4506])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f499])).

cnf(c_5192,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,sK16))
    | r2_hidden(X0,sK16) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_10012,plain,
    ( r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK7(sK15,sK17),sK16)
    | ~ r2_hidden(sK7(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_5192])).

cnf(c_10013,plain,
    ( r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK15,sK16)) = iProver_top
    | r2_hidden(sK7(sK15,sK17),sK16) = iProver_top
    | r2_hidden(sK7(sK15,sK17),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10012])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f320])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f314])).

cnf(c_725,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57,c_52])).

cnf(c_726,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_725])).

cnf(c_4854,plain,
    ( ~ r1_xboole_0(sK17,X0)
    | ~ r2_hidden(sK7(sK15,sK17),X0)
    | ~ r2_hidden(sK7(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_7293,plain,
    ( ~ r1_xboole_0(sK17,sK16)
    | ~ r2_hidden(sK7(sK15,sK17),sK16)
    | ~ r2_hidden(sK7(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_4854])).

cnf(c_7294,plain,
    ( r1_xboole_0(sK17,sK16) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK16) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK17) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7293])).

cnf(c_4822,plain,
    ( ~ r2_hidden(sK7(sK15,sK17),X0)
    | r2_hidden(sK7(sK15,sK17),k4_xboole_0(X0,sK15))
    | r2_hidden(sK7(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7207,plain,
    ( r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK17,sK15))
    | ~ r2_hidden(sK7(sK15,sK17),sK17)
    | r2_hidden(sK7(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_4822])).

cnf(c_7208,plain,
    ( r2_hidden(sK7(sK15,sK17),k4_xboole_0(sK17,sK15)) = iProver_top
    | r2_hidden(sK7(sK15,sK17),sK17) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7207])).

cnf(c_5280,plain,
    ( ~ r1_xboole_0(sK15,X0)
    | ~ r2_hidden(sK7(sK15,sK17),X0)
    | ~ r2_hidden(sK7(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_6319,plain,
    ( ~ r1_xboole_0(sK15,sK16)
    | ~ r2_hidden(sK7(sK15,sK17),sK16)
    | ~ r2_hidden(sK7(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_5280])).

cnf(c_6320,plain,
    ( r1_xboole_0(sK15,sK16) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK16) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6319])).

cnf(c_46,plain,
    ( ~ r2_hidden(sK7(X0,X1),X1)
    | ~ r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f307])).

cnf(c_4746,plain,
    ( ~ r2_hidden(sK7(sK15,sK17),sK17)
    | ~ r2_hidden(sK7(sK15,sK17),sK15)
    | sK15 = sK17 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_4760,plain,
    ( sK15 = sK17
    | r2_hidden(sK7(sK15,sK17),sK17) != iProver_top
    | r2_hidden(sK7(sK15,sK17),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4746])).

cnf(c_47,plain,
    ( r2_hidden(sK7(X0,X1),X1)
    | r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f306])).

cnf(c_4747,plain,
    ( r2_hidden(sK7(sK15,sK17),sK17)
    | r2_hidden(sK7(sK15,sK17),sK15)
    | sK15 = sK17 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_4758,plain,
    ( sK15 = sK17
    | r2_hidden(sK7(sK15,sK17),sK17) = iProver_top
    | r2_hidden(sK7(sK15,sK17),sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4747])).

cnf(c_152,negated_conjecture,
    ( sK15 != sK17 ),
    inference(cnf_transformation,[],[f416])).

cnf(c_153,negated_conjecture,
    ( r1_xboole_0(sK17,sK16) ),
    inference(cnf_transformation,[],[f415])).

cnf(c_162,plain,
    ( r1_xboole_0(sK17,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_154,negated_conjecture,
    ( r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f414])).

cnf(c_161,plain,
    ( r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_78194,c_60747,c_27458,c_13631,c_10013,c_7294,c_7208,c_6320,c_4760,c_4758,c_152,c_162,c_161])).

%------------------------------------------------------------------------------
