%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0041+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 386 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f90])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f139])).

fof(f141,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f140,f141])).

fof(f194,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f153,plain,(
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

fof(f154,plain,(
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
    inference(flattening,[],[f153])).

fof(f155,plain,(
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
    inference(rectify,[],[f154])).

fof(f156,plain,(
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

fof(f157,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f155,f156])).

fof(f209,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f157])).

fof(f331,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f209])).

fof(f210,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f157])).

fof(f330,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f210])).

fof(f211,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f157])).

fof(f329,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f211])).

fof(f196,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f68,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(negated_conjecture,[],[f68])).

fof(f127,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f184,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15))
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f185,plain,
    ( ~ r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15))
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f127,f184])).

fof(f288,plain,(
    ~ r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)) ),
    inference(cnf_transformation,[],[f185])).

fof(f287,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f185])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f194])).

cnf(c_3944,plain,
    ( ~ r1_tarski(X0,sK16)
    | ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),X0)
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK16) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5897,plain,
    ( ~ r1_tarski(sK15,sK16)
    | ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK15)
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK16) ),
    inference(instantiation,[status(thm)],[c_3944])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f331])).

cnf(c_3854,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,X0))
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK17) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_5574,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,sK16))
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK17) ),
    inference(instantiation,[status(thm)],[c_3854])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f330])).

cnf(c_3644,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,sK16))
    | ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK16) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f329])).

cnf(c_3604,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,sK15))
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK15)
    | ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),sK17) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f196])).

cnf(c_3546,plain,
    ( r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15))
    | ~ r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,sK15)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f195])).

cnf(c_3549,plain,
    ( r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15))
    | r2_hidden(sK1(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)),k4_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_99,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK17,sK16),k4_xboole_0(sK17,sK15)) ),
    inference(cnf_transformation,[],[f288])).

cnf(c_100,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f287])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5897,c_5574,c_3644,c_3604,c_3546,c_3549,c_99,c_100])).

%------------------------------------------------------------------------------
