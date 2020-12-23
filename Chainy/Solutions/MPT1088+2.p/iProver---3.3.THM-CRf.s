%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1088+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 39.71s
% Output     : CNFRefutation 39.71s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1718,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1719,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k6_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1718])).

fof(f3645,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k6_subset_1(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1719])).

fof(f5086,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k6_subset_1(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k6_subset_1(sK601,sK602))
      & v1_finset_1(sK601) ) ),
    introduced(choice_axiom,[])).

fof(f5087,plain,
    ( ~ v1_finset_1(k6_subset_1(sK601,sK602))
    & v1_finset_1(sK601) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK601,sK602])],[f3645,f5086])).

fof(f8386,plain,(
    ~ v1_finset_1(k6_subset_1(sK601,sK602)) ),
    inference(cnf_transformation,[],[f5087])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5867,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f1712,axiom,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3637,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1712])).

fof(f8378,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k4_xboole_0(X0,X1))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f3637])).

fof(f8385,plain,(
    v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f5087])).

cnf(c_3271,negated_conjecture,
    ( ~ v1_finset_1(k6_subset_1(sK601,sK602)) ),
    inference(cnf_transformation,[],[f8386])).

cnf(c_47119,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_766,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5867])).

cnf(c_124080,plain,
    ( v1_finset_1(k6_subset_1(X0,X1))
    | ~ v1_finset_1(k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_47119,c_766])).

cnf(c_124095,plain,
    ( ~ v1_finset_1(k4_xboole_0(sK601,sK602)) ),
    inference(resolution,[status(thm)],[c_3271,c_124080])).

cnf(c_3264,plain,
    ( ~ v1_finset_1(X0)
    | v1_finset_1(k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8378])).

cnf(c_124125,plain,
    ( ~ v1_finset_1(sK601) ),
    inference(resolution,[status(thm)],[c_124095,c_3264])).

cnf(c_3272,negated_conjecture,
    ( v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f8385])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124125,c_3272])).

%------------------------------------------------------------------------------
