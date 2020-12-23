%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0568+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 25.84s
% Output     : CNFRefutation 25.84s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  88 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f736,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3092,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f736])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1944,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3730,plain,(
    ! [X0] : o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f3092,f1944,f1944])).

fof(f752,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1383,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f752])).

fof(f3112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1383])).

fof(f738,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1365,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f1366,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1365])).

fof(f3095,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1366])).

fof(f3733,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | o_0_0_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3095,f1944,f1944])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2693,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2630,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3215,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2630,f1944])).

fof(f3632,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2693,f3215])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1262,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f2941,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1262])).

fof(f757,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f758,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f757])).

fof(f1388,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f758])).

fof(f1919,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK159) ),
    introduced(choice_axiom,[])).

fof(f1920,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK159) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159])],[f1388,f1919])).

fof(f3117,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK159) ),
    inference(cnf_transformation,[],[f1920])).

fof(f3739,plain,(
    o_0_0_xboole_0 != k10_relat_1(o_0_0_xboole_0,sK159) ),
    inference(definition_unfolding,[],[f3117,f1944,f1944])).

cnf(c_1141,plain,
    ( k9_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3730])).

cnf(c_86870,plain,
    ( k9_relat_1(o_0_0_xboole_0,k10_relat_1(o_0_0_xboole_0,sK159)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1161,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3112])).

cnf(c_72604,plain,
    ( r1_tarski(k10_relat_1(o_0_0_xboole_0,sK159),k1_relat_1(o_0_0_xboole_0))
    | ~ v1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1144,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3733])).

cnf(c_61324,plain,
    ( ~ r1_tarski(k10_relat_1(o_0_0_xboole_0,sK159),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,k10_relat_1(o_0_0_xboole_0,sK159)) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k10_relat_1(o_0_0_xboole_0,sK159) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_61326,plain,
    ( ~ r1_tarski(k10_relat_1(o_0_0_xboole_0,sK159),k1_relat_1(o_0_0_xboole_0))
    | ~ v1_relat_1(o_0_0_xboole_0)
    | k9_relat_1(o_0_0_xboole_0,k10_relat_1(o_0_0_xboole_0,sK159)) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k10_relat_1(o_0_0_xboole_0,sK159) ),
    inference(instantiation,[status(thm)],[c_61324])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3632])).

cnf(c_990,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f2941])).

cnf(c_1914,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1166,negated_conjecture,
    ( o_0_0_xboole_0 != k10_relat_1(o_0_0_xboole_0,sK159) ),
    inference(cnf_transformation,[],[f3739])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86870,c_72604,c_61326,c_743,c_1914,c_1166])).

%------------------------------------------------------------------------------
