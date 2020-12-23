%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0537+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 18.61s
% Output     : CNFRefutation 18.61s
% Verified   : 
% Statistics : Number of formulae       :   31 (  40 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  79 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1249,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f1250,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1249])).

fof(f2908,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1250])).

fof(f160,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f901,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f160])).

fof(f2046,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f901])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2593,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2530,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1844,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3060,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2530,f1844])).

fof(f3477,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2593,f3060])).

fof(f713,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f714,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f713])).

fof(f1306,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f714])).

fof(f1819,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK151)
      & v1_relat_1(sK151) ) ),
    introduced(choice_axiom,[])).

fof(f1820,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK151)
    & v1_relat_1(sK151) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK151])],[f1306,f1819])).

fof(f2959,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK151) ),
    inference(cnf_transformation,[],[f1820])).

fof(f3565,plain,(
    o_0_0_xboole_0 != k8_relat_1(o_0_0_xboole_0,sK151) ),
    inference(definition_unfolding,[],[f2959,f1844,f1844])).

fof(f2958,plain,(
    v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f1820])).

cnf(c_1058,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2908])).

cnf(c_54457,plain,
    ( ~ v1_relat_1(sK151)
    | v1_xboole_0(k8_relat_1(o_0_0_xboole_0,sK151))
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_208,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2046])).

cnf(c_50970,plain,
    ( ~ v1_xboole_0(k8_relat_1(o_0_0_xboole_0,sK151))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 = k8_relat_1(o_0_0_xboole_0,sK151) ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3477])).

cnf(c_1107,negated_conjecture,
    ( o_0_0_xboole_0 != k8_relat_1(o_0_0_xboole_0,sK151) ),
    inference(cnf_transformation,[],[f3565])).

cnf(c_1108,negated_conjecture,
    ( v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f2958])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54457,c_50970,c_743,c_1107,c_1108])).

%------------------------------------------------------------------------------
