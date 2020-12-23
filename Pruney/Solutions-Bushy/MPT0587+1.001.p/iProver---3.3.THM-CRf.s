%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0587+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:40 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   31 (  64 expanded)
%              Number of clauses        :   13 (  21 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 ( 107 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,plain,(
    k4_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f17,f13,f13])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_34,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_35,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_34])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_58,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK1))) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_35,c_0])).

cnf(c_1,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_61,plain,
    ( k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) = k3_xboole_0(k1_relat_1(sK1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_35,c_1])).

cnf(c_62,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_61,c_35])).

cnf(c_64,plain,
    ( k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) = k4_xboole_0(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_58,c_62])).

cnf(c_3,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_65,plain,
    ( k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_64,c_3])).

cnf(c_68,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_65])).


%------------------------------------------------------------------------------
