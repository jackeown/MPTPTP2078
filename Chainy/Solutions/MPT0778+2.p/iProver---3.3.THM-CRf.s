%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0778+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 23.77s
% Output     : CNFRefutation 23.77s
% Verified   : 
% Statistics : Number of formulae       :   27 (  53 expanded)
%              Number of clauses        :   11 (  16 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 (  86 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3118,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3270,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f5113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f3118,f3270,f3270])).

fof(f1161,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1162,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f1161])).

fof(f2310,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1162])).

fof(f3109,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK294,sK292),sK293) != k2_wellord1(k2_wellord1(sK294,sK293),sK292)
      & v1_relat_1(sK294) ) ),
    introduced(choice_axiom,[])).

fof(f3110,plain,
    ( k2_wellord1(k2_wellord1(sK294,sK292),sK293) != k2_wellord1(k2_wellord1(sK294,sK293),sK292)
    & v1_relat_1(sK294) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK292,sK293,sK294])],[f2310,f3109])).

fof(f5087,plain,(
    v1_relat_1(sK294) ),
    inference(cnf_transformation,[],[f3110])).

fof(f1160,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2309,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1160])).

fof(f5086,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2309])).

fof(f5778,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f5086,f3270])).

fof(f5088,plain,(
    k2_wellord1(k2_wellord1(sK294,sK292),sK293) != k2_wellord1(k2_wellord1(sK294,sK293),sK292) ),
    inference(cnf_transformation,[],[f3110])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5113])).

cnf(c_1958,negated_conjecture,
    ( v1_relat_1(sK294) ),
    inference(cnf_transformation,[],[f5087])).

cnf(c_54906,plain,
    ( v1_relat_1(sK294) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1958])).

cnf(c_1956,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5778])).

cnf(c_54907,plain,
    ( k2_wellord1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_70586,plain,
    ( k2_wellord1(sK294,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_wellord1(k2_wellord1(sK294,X0),X1) ),
    inference(superposition,[status(thm)],[c_54906,c_54907])).

cnf(c_77403,plain,
    ( k2_wellord1(sK294,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_wellord1(k2_wellord1(sK294,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_70586])).

cnf(c_77798,plain,
    ( k2_wellord1(k2_wellord1(sK294,X0),X1) = k2_wellord1(k2_wellord1(sK294,X1),X0) ),
    inference(superposition,[status(thm)],[c_77403,c_70586])).

cnf(c_1957,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK294,sK292),sK293) != k2_wellord1(k2_wellord1(sK294,sK293),sK292) ),
    inference(cnf_transformation,[],[f5088])).

cnf(c_78075,plain,
    ( k2_wellord1(k2_wellord1(sK294,sK292),sK293) != k2_wellord1(k2_wellord1(sK294,sK292),sK293) ),
    inference(demodulation,[status(thm)],[c_77798,c_1957])).

cnf(c_78076,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_78075])).

%------------------------------------------------------------------------------
