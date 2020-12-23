%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0027+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:13 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
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
fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f238,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f163,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f52])).

fof(f102,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f103,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f102])).

fof(f158,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK15,sK16) != sK14
      & ! [X3] :
          ( r1_tarski(X3,sK14)
          | ~ r1_tarski(X3,sK16)
          | ~ r1_tarski(X3,sK15) )
      & r1_tarski(sK14,sK16)
      & r1_tarski(sK14,sK15) ) ),
    introduced(choice_axiom,[])).

fof(f159,plain,
    ( k3_xboole_0(sK15,sK16) != sK14
    & ! [X3] :
        ( r1_tarski(X3,sK14)
        | ~ r1_tarski(X3,sK16)
        | ~ r1_tarski(X3,sK15) )
    & r1_tarski(sK14,sK16)
    & r1_tarski(sK14,sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f103,f158])).

fof(f245,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK14)
      | ~ r1_tarski(X3,sK16)
      | ~ r1_tarski(X3,sK15) ) ),
    inference(cnf_transformation,[],[f159])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f98])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f154])).

fof(f226,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f246,plain,(
    k3_xboole_0(sK15,sK16) != sK14 ),
    inference(cnf_transformation,[],[f159])).

fof(f244,plain,(
    r1_tarski(sK14,sK16) ),
    inference(cnf_transformation,[],[f159])).

fof(f243,plain,(
    r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f238])).

cnf(c_3096,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_5435,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3096])).

cnf(c_82,negated_conjecture,
    ( r1_tarski(X0,sK14)
    | ~ r1_tarski(X0,sK16)
    | ~ r1_tarski(X0,sK15) ),
    inference(cnf_transformation,[],[f245])).

cnf(c_3092,plain,
    ( r1_tarski(X0,sK14) = iProver_top
    | r1_tarski(X0,sK16) != iProver_top
    | r1_tarski(X0,sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_5671,plain,
    ( r1_tarski(k3_xboole_0(X0,sK16),sK14) = iProver_top
    | r1_tarski(k3_xboole_0(X0,sK16),sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_5435,c_3092])).

cnf(c_6263,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK16),sK14) = iProver_top ),
    inference(superposition,[status(thm)],[c_3096,c_5671])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f240])).

cnf(c_4446,plain,
    ( r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    | ~ r1_tarski(sK14,sK16)
    | ~ r1_tarski(sK14,sK15) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_4447,plain,
    ( r1_tarski(sK14,k3_xboole_0(sK15,sK16)) = iProver_top
    | r1_tarski(sK14,sK16) != iProver_top
    | r1_tarski(sK14,sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4446])).

cnf(c_62,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f226])).

cnf(c_3761,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK16),sK14)
    | ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    | k3_xboole_0(sK15,sK16) = sK14 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_3762,plain,
    ( k3_xboole_0(sK15,sK16) = sK14
    | r1_tarski(k3_xboole_0(sK15,sK16),sK14) != iProver_top
    | r1_tarski(sK14,k3_xboole_0(sK15,sK16)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3761])).

cnf(c_81,negated_conjecture,
    ( k3_xboole_0(sK15,sK16) != sK14 ),
    inference(cnf_transformation,[],[f246])).

cnf(c_83,negated_conjecture,
    ( r1_tarski(sK14,sK16) ),
    inference(cnf_transformation,[],[f244])).

cnf(c_98,plain,
    ( r1_tarski(sK14,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_84,negated_conjecture,
    ( r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f243])).

cnf(c_97,plain,
    ( r1_tarski(sK14,sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6263,c_4447,c_3762,c_81,c_98,c_97])).

%------------------------------------------------------------------------------
