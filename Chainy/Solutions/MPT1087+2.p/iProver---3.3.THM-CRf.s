%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 39.18s
% Output     : CNFRefutation 39.18s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  46 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3634,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1711])).

fof(f8373,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f3634])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5239,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f10034,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f8373,f5239])).

fof(f1716,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1717,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1716])).

fof(f3641,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1717])).

fof(f5082,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK601,sK602))
      & v1_finset_1(sK601) ) ),
    introduced(choice_axiom,[])).

fof(f5083,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK601,sK602))
    & v1_finset_1(sK601) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK601,sK602])],[f3641,f5082])).

fof(f8380,plain,(
    ~ v1_finset_1(k3_xboole_0(sK601,sK602)) ),
    inference(cnf_transformation,[],[f5083])).

fof(f10037,plain,(
    ~ v1_finset_1(k4_xboole_0(sK601,k4_xboole_0(sK601,sK602))) ),
    inference(definition_unfolding,[],[f8380,f5239])).

fof(f8379,plain,(
    v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f5083])).

cnf(c_3263,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f10034])).

cnf(c_124028,plain,
    ( v1_finset_1(k4_xboole_0(sK601,k4_xboole_0(sK601,sK602)))
    | ~ v1_finset_1(sK601) ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_3269,negated_conjecture,
    ( ~ v1_finset_1(k4_xboole_0(sK601,k4_xboole_0(sK601,sK602))) ),
    inference(cnf_transformation,[],[f10037])).

cnf(c_3270,negated_conjecture,
    ( v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f8379])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124028,c_3269,c_3270])).

%------------------------------------------------------------------------------
