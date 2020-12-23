%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0052+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:15 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 153 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f102])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f157])).

fof(f159,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f158,f159])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f216,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f81,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f145,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f71,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f311,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f71])).

fof(f92,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f150,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f151,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f150])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f196,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f196])).

fof(f272,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f197])).

fof(f82,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(negated_conjecture,[],[f82])).

fof(f146,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) != X1
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f204,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) != X1
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)) != sK16
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f205,plain,
    ( k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)) != sK16
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f146,f204])).

fof(f324,plain,(
    k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)) != sK16 ),
    inference(cnf_transformation,[],[f205])).

fof(f323,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f205])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f215])).

cnf(c_7983,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK15),k4_xboole_0(sK16,sK15))
    | r2_hidden(sK1(k4_xboole_0(sK16,sK15),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK16,sK15)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f216])).

cnf(c_7984,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK15),k4_xboole_0(sK16,sK15))
    | ~ r2_hidden(sK1(k4_xboole_0(sK16,sK15),k4_xboole_0(sK16,sK15)),k4_xboole_0(sK16,sK15)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_114,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f322])).

cnf(c_5541,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),k4_xboole_0(sK16,sK15))
    | r1_tarski(sK16,k2_xboole_0(sK15,k4_xboole_0(sK16,sK15))) ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_103,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f311])).

cnf(c_5137,plain,
    ( r1_tarski(k4_xboole_0(sK16,sK15),sK16) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f333])).

cnf(c_4935,plain,
    ( ~ r1_tarski(k4_xboole_0(sK16,sK15),sK16)
    | r1_tarski(k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)),sK16)
    | ~ r1_tarski(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_62,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f272])).

cnf(c_4597,plain,
    ( ~ r1_tarski(k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)),sK16)
    | ~ r1_tarski(sK16,k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)))
    | k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)) = sK16 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_115,negated_conjecture,
    ( k2_xboole_0(sK15,k4_xboole_0(sK16,sK15)) != sK16 ),
    inference(cnf_transformation,[],[f324])).

cnf(c_116,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f323])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7983,c_7984,c_5541,c_5137,c_4935,c_4597,c_115,c_116])).

%------------------------------------------------------------------------------
