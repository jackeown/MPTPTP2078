%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0009+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:14 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  63 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,conjecture,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] : ~ r1_tarski(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,
    ( ? [X0] : ~ r1_tarski(k1_xboole_0,X0)
   => ~ r1_tarski(k1_xboole_0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f14])).

fof(f21,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_2,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_72,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | sK1 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_73,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_90,plain,
    ( ~ v1_xboole_0(X0)
    | sK0(k1_xboole_0,sK1) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_73])).

cnf(c_91,plain,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_90])).

cnf(c_113,plain,
    ( k1_xboole_0 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_91])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_108,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_109,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113,c_109])).


%------------------------------------------------------------------------------
