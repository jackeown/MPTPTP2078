%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0035+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:13 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 181 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   5 average)
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

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f82])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f127])).

fof(f129,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f128,f129])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f184,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f110])).

fof(f170,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK14(X0,X1,X2),X0)
        & r1_tarski(sK14(X0,X1,X2),X2)
        & r1_tarski(sK14(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f171,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK14(X0,X1,X2),X0)
        & r1_tarski(sK14(X0,X1,X2),X2)
        & r1_tarski(sK14(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f111,f170])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK14(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK14(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f60,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f60])).

fof(f115,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,X1) != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f172,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(X0,X1) != X0
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK15,sK16) != sK15
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f173,plain,
    ( k3_xboole_0(sK15,sK16) != sK15
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f115,f172])).

fof(f268,plain,(
    k3_xboole_0(sK15,sK16) != sK15 ),
    inference(cnf_transformation,[],[f173])).

fof(f267,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f183])).

cnf(c_4413,plain,
    ( r1_tarski(sK15,sK15)
    | r2_hidden(sK1(sK15,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_4414,plain,
    ( r1_tarski(sK15,sK15)
    | ~ r2_hidden(sK1(sK15,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_83,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK14(X0,X1,X2),X1)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f257])).

cnf(c_4021,plain,
    ( r1_tarski(sK14(sK15,sK15,sK16),sK15)
    | ~ r1_tarski(sK15,sK16)
    | ~ r1_tarski(sK15,sK15)
    | k3_xboole_0(sK15,sK16) = sK15 ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_81,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK14(X0,X1,X2),X0)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f259])).

cnf(c_3988,plain,
    ( ~ r1_tarski(sK14(sK15,sK15,sK16),sK15)
    | ~ r1_tarski(sK15,sK16)
    | ~ r1_tarski(sK15,sK15)
    | k3_xboole_0(sK15,sK16) = sK15 ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_91,negated_conjecture,
    ( k3_xboole_0(sK15,sK16) != sK15 ),
    inference(cnf_transformation,[],[f268])).

cnf(c_92,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f267])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4413,c_4414,c_4021,c_3988,c_91,c_92])).

%------------------------------------------------------------------------------
