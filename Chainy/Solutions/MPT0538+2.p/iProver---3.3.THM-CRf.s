%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0538+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 15.89s
% Output     : CNFRefutation 15.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  57 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f693,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1280,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f2940,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1280])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f856,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f1985,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f856])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1846,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3150,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f1985,f1846,f1846])).

fof(f714,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f715,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f714])).

fof(f1308,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f715])).

fof(f1821,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK151,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f1822,plain,(
    k1_xboole_0 != k8_relat_1(sK151,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151])],[f1308,f1821])).

fof(f2961,plain,(
    k1_xboole_0 != k8_relat_1(sK151,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1822])).

fof(f3568,plain,(
    o_0_0_xboole_0 != k8_relat_1(sK151,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2961,f1846,f1846])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2595,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2532,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3062,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2532,f1846])).

fof(f3479,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2595,f3062])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1222,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f2843,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1222])).

cnf(c_1087,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f2940])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3150])).

cnf(c_1108,negated_conjecture,
    ( o_0_0_xboole_0 != k8_relat_1(sK151,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3568])).

cnf(c_42099,plain,
    ( ~ r1_tarski(k8_relat_1(sK151,o_0_0_xboole_0),o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_146,c_1108])).

cnf(c_42238,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_1087,c_42099])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3479])).

cnf(c_990,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f2843])).

cnf(c_1718,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42238,c_743,c_1718])).

%------------------------------------------------------------------------------
