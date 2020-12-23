%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0113+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  216 ( 262 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f286,plain,(
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

fof(f287,plain,(
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
    inference(flattening,[],[f286])).

fof(f288,plain,(
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
    inference(rectify,[],[f287])).

fof(f289,plain,(
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

fof(f290,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f288,f289])).

fof(f352,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f290])).

fof(f670,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f352])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f171,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f171])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f272])).

fof(f274,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f273,f274])).

fof(f336,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f275])).

fof(f86,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f455,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f86])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f201,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f202,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f201])).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f202])).

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

fof(f166,plain,(
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

fof(f177,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f166])).

fof(f305,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f177,f305])).

fof(f382,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f306])).

fof(f383,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f306])).

fof(f54,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f54])).

fof(f189,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f320,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK13,sK15)
        | ~ r1_tarski(sK13,sK14) )
      & r1_tarski(sK13,k4_xboole_0(sK14,sK15)) ) ),
    introduced(choice_axiom,[])).

fof(f321,plain,
    ( ( ~ r1_xboole_0(sK13,sK15)
      | ~ r1_tarski(sK13,sK14) )
    & r1_tarski(sK13,k4_xboole_0(sK14,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f189,f320])).

fof(f420,plain,
    ( ~ r1_xboole_0(sK13,sK15)
    | ~ r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f321])).

fof(f419,plain,(
    r1_tarski(sK13,k4_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f321])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f670])).

cnf(c_8431,plain,
    ( ~ r2_hidden(sK9(sK13,sK15),k4_xboole_0(X0,sK15))
    | ~ r2_hidden(sK9(sK13,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_25673,plain,
    ( ~ r2_hidden(sK9(sK13,sK15),k4_xboole_0(sK14,sK15))
    | ~ r2_hidden(sK9(sK13,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_8431])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f336])).

cnf(c_8525,plain,
    ( ~ r1_tarski(sK13,X0)
    | r2_hidden(sK9(sK13,sK15),X0)
    | ~ r2_hidden(sK9(sK13,sK15),sK13) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_21149,plain,
    ( ~ r1_tarski(sK13,k4_xboole_0(sK14,sK15))
    | r2_hidden(sK9(sK13,sK15),k4_xboole_0(sK14,sK15))
    | ~ r2_hidden(sK9(sK13,sK15),sK13) ),
    inference(instantiation,[status(thm)],[c_8525])).

cnf(c_126,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f455])).

cnf(c_15217,plain,
    ( r1_tarski(k4_xboole_0(sK14,sK15),sK14) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f434])).

cnf(c_8939,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK13,X0)
    | r1_tarski(sK13,X1) ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_13179,plain,
    ( ~ r1_tarski(k4_xboole_0(sK14,sK15),X0)
    | r1_tarski(sK13,X0)
    | ~ r1_tarski(sK13,k4_xboole_0(sK14,sK15)) ),
    inference(instantiation,[status(thm)],[c_8939])).

cnf(c_15216,plain,
    ( ~ r1_tarski(k4_xboole_0(sK14,sK15),sK14)
    | ~ r1_tarski(sK13,k4_xboole_0(sK14,sK15))
    | r1_tarski(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_13179])).

cnf(c_56,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X0) ),
    inference(cnf_transformation,[],[f382])).

cnf(c_7373,plain,
    ( r1_xboole_0(sK13,sK15)
    | r2_hidden(sK9(sK13,sK15),sK13) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_55,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X1) ),
    inference(cnf_transformation,[],[f383])).

cnf(c_7370,plain,
    ( r1_xboole_0(sK13,sK15)
    | r2_hidden(sK9(sK13,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_90,negated_conjecture,
    ( ~ r1_xboole_0(sK13,sK15)
    | ~ r1_tarski(sK13,sK14) ),
    inference(cnf_transformation,[],[f420])).

cnf(c_91,negated_conjecture,
    ( r1_tarski(sK13,k4_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f419])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25673,c_21149,c_15217,c_15216,c_7373,c_7370,c_90,c_91])).

%------------------------------------------------------------------------------
