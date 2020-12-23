%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0268+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:32 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :   36 (  71 expanded)
%              Number of clauses        :   15 (  23 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 172 expanded)
%              Number of equality atoms :   23 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f602,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f880,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f602])).

fof(f364,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f365,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f364])).

fof(f533,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f365])).

fof(f676,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f533])).

fof(f677,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK36,sK35)
        | k4_xboole_0(sK35,k1_tarski(sK36)) != sK35 )
      & ( ~ r2_hidden(sK36,sK35)
        | k4_xboole_0(sK35,k1_tarski(sK36)) = sK35 ) ) ),
    introduced(choice_axiom,[])).

fof(f678,plain,
    ( ( r2_hidden(sK36,sK35)
      | k4_xboole_0(sK35,k1_tarski(sK36)) != sK35 )
    & ( ~ r2_hidden(sK36,sK35)
      | k4_xboole_0(sK35,k1_tarski(sK36)) = sK35 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f676,f677])).

fof(f1180,plain,
    ( r2_hidden(sK36,sK35)
    | k4_xboole_0(sK35,k1_tarski(sK36)) != sK35 ),
    inference(cnf_transformation,[],[f678])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f379,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f722,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f379])).

fof(f357,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f527,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f357])).

fof(f1169,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f527])).

fof(f1179,plain,
    ( ~ r2_hidden(sK36,sK35)
    | k4_xboole_0(sK35,k1_tarski(sK36)) = sK35 ),
    inference(cnf_transformation,[],[f678])).

fof(f881,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f602])).

fof(f355,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f1167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f525])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f880])).

cnf(c_488,negated_conjecture,
    ( r2_hidden(sK36,sK35)
    | k4_xboole_0(sK35,k1_tarski(sK36)) != sK35 ),
    inference(cnf_transformation,[],[f1180])).

cnf(c_25219,plain,
    ( ~ r1_xboole_0(sK35,k1_tarski(sK36))
    | r2_hidden(sK36,sK35) ),
    inference(resolution,[status(thm)],[c_201,c_488])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f722])).

cnf(c_478,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1169])).

cnf(c_19196,plain,
    ( r1_xboole_0(X0,k1_tarski(X1))
    | r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_44,c_478])).

cnf(c_25976,plain,
    ( r2_hidden(sK36,sK35) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25219,c_19196])).

cnf(c_489,negated_conjecture,
    ( ~ r2_hidden(sK36,sK35)
    | k4_xboole_0(sK35,k1_tarski(sK36)) = sK35 ),
    inference(cnf_transformation,[],[f1179])).

cnf(c_25983,plain,
    ( k4_xboole_0(sK35,k1_tarski(sK36)) = sK35 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_25976,c_489])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f881])).

cnf(c_25991,plain,
    ( r1_xboole_0(sK35,k1_tarski(sK36)) ),
    inference(resolution,[status(thm)],[c_25983,c_200])).

cnf(c_26664,plain,
    ( r1_xboole_0(k1_tarski(sK36),sK35) ),
    inference(resolution,[status(thm)],[c_25991,c_44])).

cnf(c_476,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1167])).

cnf(c_22040,plain,
    ( ~ r1_xboole_0(k1_tarski(sK36),sK35)
    | ~ r2_hidden(sK36,sK35) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26664,c_25976,c_22040])).

%------------------------------------------------------------------------------
