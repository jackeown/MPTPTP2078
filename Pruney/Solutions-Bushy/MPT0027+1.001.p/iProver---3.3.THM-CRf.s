%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0027+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:17 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of clauses        :   26 (  28 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 270 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK2) != sK0
      & ! [X3] :
          ( r1_tarski(X3,sK0)
          | ~ r1_tarski(X3,sK2)
          | ~ r1_tarski(X3,sK1) )
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( k3_xboole_0(sK1,sK2) != sK0
    & ! [X3] :
        ( r1_tarski(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X3,sK1) )
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f23,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    k3_xboole_0(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | k3_xboole_0(sK1,sK2) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_455,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | k3_xboole_0(sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_585,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK1),sK2)
    | r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_461,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_449,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_134,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_411,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_364,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_366,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_348,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | sK0 = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_323,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_135,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_307,plain,
    ( k3_xboole_0(sK1,sK2) != X0
    | k3_xboole_0(sK1,sK2) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_322,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = sK0
    | sK0 != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_318,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(X0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_311,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) != sK0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_585,c_461,c_449,c_411,c_366,c_348,c_323,c_322,c_318,c_311,c_6,c_8,c_9])).


%------------------------------------------------------------------------------
