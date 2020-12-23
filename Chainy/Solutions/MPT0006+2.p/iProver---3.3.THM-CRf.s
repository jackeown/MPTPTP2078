%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 202 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f59,f60])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f35,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f95,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
            | ~ r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) )
   => ( ! [X2] :
          ( r2_hidden(X2,sK11)
          | ~ r2_hidden(X2,sK12) )
      & r2_xboole_0(sK11,sK12) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK11)
        | ~ r2_hidden(X2,sK12) )
    & r2_xboole_0(sK11,sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f53,f95])).

fof(f161,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK11)
      | ~ r2_hidden(X2,sK12) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f78])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f24,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f24])).

fof(f136,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f160,plain,(
    r2_xboole_0(sK11,sK12) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2544,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_61,negated_conjecture,
    ( ~ r2_hidden(X0,sK12)
    | r2_hidden(X0,sK11) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_2498,plain,
    ( r2_hidden(X0,sK12) != iProver_top
    | r2_hidden(X0,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_5269,plain,
    ( r1_tarski(sK12,X0) = iProver_top
    | r2_hidden(sK1(sK12,X0),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_2544,c_2498])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2545,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8291,plain,
    ( r1_tarski(sK12,sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_2545])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3202,plain,
    ( ~ r1_tarski(X0,sK11)
    | r2_xboole_0(X0,sK11)
    | X0 = sK11 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3555,plain,
    ( ~ r1_tarski(sK12,sK11)
    | r2_xboole_0(sK12,sK11)
    | sK12 = sK11 ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_3557,plain,
    ( sK12 = sK11
    | r1_tarski(sK12,sK11) != iProver_top
    | r2_xboole_0(sK12,sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3555])).

cnf(c_37,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3348,plain,
    ( ~ r2_xboole_0(sK12,sK12) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1436,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2943,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(sK11,sK12)
    | X1 != sK12
    | X0 != sK11 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_3049,plain,
    ( r2_xboole_0(X0,sK12)
    | ~ r2_xboole_0(sK11,sK12)
    | X0 != sK11
    | sK12 != sK12 ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_3347,plain,
    ( r2_xboole_0(sK12,sK12)
    | ~ r2_xboole_0(sK11,sK12)
    | sK12 != sK12
    | sK12 != sK11 ),
    inference(instantiation,[status(thm)],[c_3049])).

cnf(c_1433,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3050,plain,
    ( sK12 = sK12 ),
    inference(instantiation,[status(thm)],[c_1433])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2929,plain,
    ( ~ r2_xboole_0(sK12,sK11)
    | ~ r2_xboole_0(sK11,sK12) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2930,plain,
    ( r2_xboole_0(sK12,sK11) != iProver_top
    | r2_xboole_0(sK11,sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2929])).

cnf(c_62,negated_conjecture,
    ( r2_xboole_0(sK11,sK12) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_63,plain,
    ( r2_xboole_0(sK11,sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8291,c_3557,c_3348,c_3347,c_3050,c_2930,c_63,c_62])).

%------------------------------------------------------------------------------
