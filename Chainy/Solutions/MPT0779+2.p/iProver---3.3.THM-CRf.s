%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0779+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 27.49s
% Output     : CNFRefutation 27.49s
% Verified   : 
% Statistics : Number of formulae       :   26 (  33 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1169,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f3155,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f1169])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3272,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f5133,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f3155,f3272])).

fof(f1162,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1163,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k2_wellord1(k2_wellord1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f1162])).

fof(f2312,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1163])).

fof(f3111,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k2_wellord1(k2_wellord1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK293,sK292) != k2_wellord1(k2_wellord1(sK293,sK292),sK292)
      & v1_relat_1(sK293) ) ),
    introduced(choice_axiom,[])).

fof(f3112,plain,
    ( k2_wellord1(sK293,sK292) != k2_wellord1(k2_wellord1(sK293,sK292),sK292)
    & v1_relat_1(sK293) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK292,sK293])],[f2312,f3111])).

fof(f5090,plain,(
    v1_relat_1(sK293) ),
    inference(cnf_transformation,[],[f3112])).

fof(f1160,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2310,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1160])).

fof(f5088,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2310])).

fof(f5781,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f5088,f3272])).

fof(f5091,plain,(
    k2_wellord1(sK293,sK292) != k2_wellord1(k2_wellord1(sK293,sK292),sK292) ),
    inference(cnf_transformation,[],[f3112])).

cnf(c_39,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f5133])).

cnf(c_1959,negated_conjecture,
    ( v1_relat_1(sK293) ),
    inference(cnf_transformation,[],[f5090])).

cnf(c_92803,plain,
    ( v1_relat_1(sK293) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_1956,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5781])).

cnf(c_92805,plain,
    ( k2_wellord1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_97476,plain,
    ( k2_wellord1(sK293,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_wellord1(k2_wellord1(sK293,X0),X1) ),
    inference(superposition,[status(thm)],[c_92803,c_92805])).

cnf(c_98564,plain,
    ( k2_wellord1(k2_wellord1(sK293,X0),X0) = k2_wellord1(sK293,X0) ),
    inference(superposition,[status(thm)],[c_39,c_97476])).

cnf(c_1958,negated_conjecture,
    ( k2_wellord1(sK293,sK292) != k2_wellord1(k2_wellord1(sK293,sK292),sK292) ),
    inference(cnf_transformation,[],[f5091])).

cnf(c_106076,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_98564,c_1958])).

%------------------------------------------------------------------------------
