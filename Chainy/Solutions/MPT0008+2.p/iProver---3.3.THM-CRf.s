%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0008+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   34 (  74 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 248 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f72])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f73,f74])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f37,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f63,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f64,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f111,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X2)
        & r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK13,sK15)
      & r1_tarski(sK14,sK15)
      & r1_tarski(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,
    ( ~ r1_tarski(sK13,sK15)
    & r1_tarski(sK14,sK15)
    & r1_tarski(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f64,f111])).

fof(f179,plain,(
    ~ r1_tarski(sK13,sK15) ),
    inference(cnf_transformation,[],[f112])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f178,plain,(
    r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f112])).

fof(f177,plain,(
    r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3618,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(sK13,sK15),X0)
    | r2_hidden(sK1(sK13,sK15),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9499,plain,
    ( ~ r1_tarski(sK14,X0)
    | r2_hidden(sK1(sK13,sK15),X0)
    | ~ r2_hidden(sK1(sK13,sK15),sK14) ),
    inference(instantiation,[status(thm)],[c_3618])).

cnf(c_12141,plain,
    ( ~ r1_tarski(sK14,sK15)
    | ~ r2_hidden(sK1(sK13,sK15),sK14)
    | r2_hidden(sK1(sK13,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_9499])).

cnf(c_3218,plain,
    ( ~ r1_tarski(sK13,X0)
    | r2_hidden(sK1(sK13,sK15),X0)
    | ~ r2_hidden(sK1(sK13,sK15),sK13) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4849,plain,
    ( ~ r1_tarski(sK13,sK14)
    | r2_hidden(sK1(sK13,sK15),sK14)
    | ~ r2_hidden(sK1(sK13,sK15),sK13) ),
    inference(instantiation,[status(thm)],[c_3218])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_62,negated_conjecture,
    ( ~ r1_tarski(sK13,sK15) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_803,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | sK15 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_62])).

cnf(c_804,plain,
    ( ~ r2_hidden(sK1(sK13,sK15),sK15) ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_796,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | sK15 != X1
    | sK13 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_62])).

cnf(c_797,plain,
    ( r2_hidden(sK1(sK13,sK15),sK13) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_63,negated_conjecture,
    ( r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_64,negated_conjecture,
    ( r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f177])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12141,c_4849,c_804,c_797,c_63,c_64])).

%------------------------------------------------------------------------------
