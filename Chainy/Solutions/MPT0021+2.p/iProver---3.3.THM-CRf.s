%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 249 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f231,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f147,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X2,X3)
                & r1_tarski(X0,X3) )
             => r1_tarski(X1,X3) )
          & r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => k2_xboole_0(X0,X2) = X1 ) ),
    inference(negated_conjecture,[],[f44])).

fof(f87,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f88,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f87])).

fof(f143,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,X2) != X1
        & ! [X3] :
            ( r1_tarski(X1,X3)
            | ~ r1_tarski(X2,X3)
            | ~ r1_tarski(X0,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK13,sK15) != sK14
      & ! [X3] :
          ( r1_tarski(sK14,X3)
          | ~ r1_tarski(sK15,X3)
          | ~ r1_tarski(sK13,X3) )
      & r1_tarski(sK15,sK14)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f144,plain,
    ( k2_xboole_0(sK13,sK15) != sK14
    & ! [X3] :
        ( r1_tarski(sK14,X3)
        | ~ r1_tarski(sK15,X3)
        | ~ r1_tarski(sK13,X3) )
    & r1_tarski(sK15,sK14)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f88,f143])).

fof(f220,plain,(
    ! [X3] :
      ( r1_tarski(sK14,X3)
      | ~ r1_tarski(sK15,X3)
      | ~ r1_tarski(sK13,X3) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f95])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f141])).

fof(f211,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f221,plain,(
    k2_xboole_0(sK13,sK15) != sK14 ),
    inference(cnf_transformation,[],[f144])).

fof(f219,plain,(
    r1_tarski(sK15,sK14) ),
    inference(cnf_transformation,[],[f144])).

fof(f218,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_84,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f231])).

cnf(c_2864,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_3888,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2864])).

cnf(c_72,negated_conjecture,
    ( r1_tarski(sK14,X0)
    | ~ r1_tarski(sK15,X0)
    | ~ r1_tarski(sK13,X0) ),
    inference(cnf_transformation,[],[f220])).

cnf(c_2870,plain,
    ( r1_tarski(sK14,X0) = iProver_top
    | r1_tarski(sK15,X0) != iProver_top
    | r1_tarski(sK13,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_4461,plain,
    ( r1_tarski(sK14,k2_xboole_0(X0,sK15)) = iProver_top
    | r1_tarski(sK13,k2_xboole_0(X0,sK15)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_2870])).

cnf(c_4525,plain,
    ( r1_tarski(sK14,k2_xboole_0(sK13,sK15)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_4461])).

cnf(c_86,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f233])).

cnf(c_3610,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),sK14)
    | ~ r1_tarski(sK15,sK14)
    | ~ r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_3611,plain,
    ( r1_tarski(k2_xboole_0(sK13,sK15),sK14) = iProver_top
    | r1_tarski(sK15,sK14) != iProver_top
    | r1_tarski(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3610])).

cnf(c_62,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f211])).

cnf(c_3485,plain,
    ( ~ r1_tarski(k2_xboole_0(sK13,sK15),sK14)
    | ~ r1_tarski(sK14,k2_xboole_0(sK13,sK15))
    | k2_xboole_0(sK13,sK15) = sK14 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_3486,plain,
    ( k2_xboole_0(sK13,sK15) = sK14
    | r1_tarski(k2_xboole_0(sK13,sK15),sK14) != iProver_top
    | r1_tarski(sK14,k2_xboole_0(sK13,sK15)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3485])).

cnf(c_71,negated_conjecture,
    ( k2_xboole_0(sK13,sK15) != sK14 ),
    inference(cnf_transformation,[],[f221])).

cnf(c_73,negated_conjecture,
    ( r1_tarski(sK15,sK14) ),
    inference(cnf_transformation,[],[f219])).

cnf(c_89,plain,
    ( r1_tarski(sK15,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_74,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f218])).

cnf(c_88,plain,
    ( r1_tarski(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4525,c_3611,c_3486,c_71,c_89,c_88])).

%------------------------------------------------------------------------------
