%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0009+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:10 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  62 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f75,f76])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f149,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f122,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f187,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f149,f122])).

fof(f38,conjecture,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f38])).

fof(f66,plain,(
    ? [X0] : ~ r1_tarski(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f39])).

fof(f113,plain,
    ( ? [X0] : ~ r1_tarski(k1_xboole_0,X0)
   => ~ r1_tarski(k1_xboole_0,sK13) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ~ r1_tarski(k1_xboole_0,sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f66,f113])).

fof(f180,plain,(
    ~ r1_tarski(k1_xboole_0,sK13) ),
    inference(cnf_transformation,[],[f114])).

fof(f198,plain,(
    ~ r1_tarski(o_0_0_xboole_0,sK13) ),
    inference(definition_unfolding,[],[f180,f122])).

cnf(c_65,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f182])).

cnf(c_2841,plain,
    ( ~ r2_hidden(sK1(o_0_0_xboole_0,sK13),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2779,plain,
    ( r1_tarski(o_0_0_xboole_0,sK13)
    | r2_hidden(sK1(o_0_0_xboole_0,sK13),o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_32,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f187])).

cnf(c_63,negated_conjecture,
    ( ~ r1_tarski(o_0_0_xboole_0,sK13) ),
    inference(cnf_transformation,[],[f198])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2841,c_2779,c_32,c_63])).

%------------------------------------------------------------------------------
