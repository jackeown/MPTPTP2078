%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0006+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:14 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 199 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
            | ~ r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) )
   => ( ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ r2_hidden(X2,sK2) )
      & r2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,sK2) )
    & r2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f15])).

fof(f25,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f24,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(X0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_522,plain,
    ( ~ r2_hidden(sK0(sK2,X0),sK2)
    | r2_hidden(sK0(sK2,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_524,plain,
    ( ~ r2_hidden(sK0(sK2,sK1),sK2)
    | r2_hidden(sK0(sK2,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_480,plain,
    ( r2_hidden(sK0(sK2,X0),sK2)
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_492,plain,
    ( r2_hidden(sK0(sK2,sK1),sK2)
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_481,plain,
    ( ~ r2_hidden(sK0(sK2,X0),X0)
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_488,plain,
    ( ~ r2_hidden(sK0(sK2,sK1),sK1)
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_467,plain,
    ( ~ r1_tarski(sK2,X0)
    | r2_xboole_0(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_469,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r2_xboole_0(sK2,sK1)
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_188,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_442,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_443,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_189,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_425,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(sK1,sK2)
    | X1 != sK2
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_427,plain,
    ( ~ r2_xboole_0(sK1,sK2)
    | r2_xboole_0(sK1,sK1)
    | sK1 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_0,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_422,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_187,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_194,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_5,plain,
    ( ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_17,plain,
    ( ~ r2_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,negated_conjecture,
    ( r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_524,c_492,c_488,c_469,c_443,c_427,c_422,c_194,c_17,c_8])).


%------------------------------------------------------------------------------
