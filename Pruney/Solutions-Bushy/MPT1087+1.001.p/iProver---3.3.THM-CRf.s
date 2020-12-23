%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1087+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:51 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   16 (  21 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k3_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f10,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_0,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_32,plain,
    ( ~ v1_finset_1(X0_32)
    | v1_finset_1(k3_xboole_0(X0_32,X0_33)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_34,plain,
    ( v1_finset_1(k3_xboole_0(sK0,sK1))
    | ~ v1_finset_1(sK0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1,negated_conjecture,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_2,negated_conjecture,
    ( v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34,c_1,c_2])).


%------------------------------------------------------------------------------
