%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:06 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :   11
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f12,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_41,plain,
    ( k3_xboole_0(X0_35,X1_35) = k3_xboole_0(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_40,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_29,plain,
    ( k2_wellord1(X0,k3_xboole_0(X1,X2)) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_30,plain,
    ( k2_wellord1(sK2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( k2_wellord1(sK2,k3_xboole_0(X0_35,X1_35)) = k2_wellord1(k2_wellord1(sK2,X0_35),X1_35) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_52,plain,
    ( k2_wellord1(sK2,k3_xboole_0(sK1,sK0)) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_40,c_39])).

cnf(c_53,plain,
    ( k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_41,c_52])).

cnf(c_54,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_53])).


%------------------------------------------------------------------------------
