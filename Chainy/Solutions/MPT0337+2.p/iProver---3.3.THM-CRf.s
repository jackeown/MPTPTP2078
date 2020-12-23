%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0337+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 39.09s
% Output     : CNFRefutation 39.09s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of clauses        :   14 (  17 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 167 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f464,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f926,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f464])).

fof(f366,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f367,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f366])).

fof(f630,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f367])).

fof(f631,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f630])).

fof(f846,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
        & ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55))
      & ! [X3,X2] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,sK55)
          | ~ r2_hidden(X2,sK54) ) ) ),
    introduced(choice_axiom,[])).

fof(f847,plain,
    ( ~ r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55))
    & ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r2_hidden(X3,sK55)
        | ~ r2_hidden(X2,sK54) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54,sK55])],[f631,f846])).

fof(f1409,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ r2_hidden(X3,sK55)
      | ~ r2_hidden(X2,sK54) ) ),
    inference(cnf_transformation,[],[f847])).

fof(f443,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f678,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f443])).

fof(f877,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK59(X0,X1),X1)
        & r2_hidden(sK59(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f878,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK59(X0,X1),X1)
        & r2_hidden(sK59(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK59])],[f678,f877])).

fof(f1527,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK59(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f878])).

fof(f1528,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK59(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f878])).

fof(f1410,plain,(
    ~ r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55)) ),
    inference(cnf_transformation,[],[f847])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f926])).

cnf(c_148509,plain,
    ( r1_xboole_0(sK59(sK55,sK59(sK54,k3_tarski(sK55))),sK59(sK54,k3_tarski(sK55)))
    | ~ r1_xboole_0(sK59(sK54,k3_tarski(sK55)),sK59(sK55,sK59(sK54,k3_tarski(sK55)))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_515,negated_conjecture,
    ( r1_xboole_0(X0,X1)
    | ~ r2_hidden(X1,sK55)
    | ~ r2_hidden(X0,sK54) ),
    inference(cnf_transformation,[],[f1409])).

cnf(c_23508,plain,
    ( r1_xboole_0(sK59(sK54,k3_tarski(sK55)),X0)
    | ~ r2_hidden(X0,sK55)
    | ~ r2_hidden(sK59(sK54,k3_tarski(sK55)),sK54) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_148458,plain,
    ( r1_xboole_0(sK59(sK54,k3_tarski(sK55)),sK59(sK55,sK59(sK54,k3_tarski(sK55))))
    | ~ r2_hidden(sK59(sK55,sK59(sK54,k3_tarski(sK55))),sK55)
    | ~ r2_hidden(sK59(sK54,k3_tarski(sK55)),sK54) ),
    inference(instantiation,[status(thm)],[c_23508])).

cnf(c_633,plain,
    ( r1_xboole_0(k3_tarski(X0),X1)
    | r2_hidden(sK59(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1527])).

cnf(c_35848,plain,
    ( r1_xboole_0(k3_tarski(sK55),sK59(sK54,k3_tarski(sK55)))
    | r2_hidden(sK59(sK55,sK59(sK54,k3_tarski(sK55))),sK55) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_632,plain,
    ( ~ r1_xboole_0(sK59(X0,X1),X1)
    | r1_xboole_0(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f1528])).

cnf(c_35849,plain,
    ( ~ r1_xboole_0(sK59(sK55,sK59(sK54,k3_tarski(sK55))),sK59(sK54,k3_tarski(sK55)))
    | r1_xboole_0(k3_tarski(sK55),sK59(sK54,k3_tarski(sK55))) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_23342,plain,
    ( r1_xboole_0(sK59(sK54,k3_tarski(sK55)),k3_tarski(sK55))
    | ~ r1_xboole_0(k3_tarski(sK55),sK59(sK54,k3_tarski(sK55))) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_18944,plain,
    ( r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55))
    | r2_hidden(sK59(sK54,k3_tarski(sK55)),sK54) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_18941,plain,
    ( ~ r1_xboole_0(sK59(sK54,k3_tarski(sK55)),k3_tarski(sK55))
    | r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55)) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_514,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(sK54),k3_tarski(sK55)) ),
    inference(cnf_transformation,[],[f1410])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_148509,c_148458,c_35848,c_35849,c_23342,c_18944,c_18941,c_514])).

%------------------------------------------------------------------------------
