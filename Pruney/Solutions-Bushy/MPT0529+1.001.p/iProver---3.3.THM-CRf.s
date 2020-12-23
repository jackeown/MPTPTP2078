%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0529+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:30 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 ( 103 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_58,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_59,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_58])).

cnf(c_68,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_59])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_71,plain,
    ( k3_xboole_0(X0_35,X1_35) = k3_xboole_0(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k3_xboole_0(X1,X2),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_51,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_52,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    inference(unflattening,[status(thm)],[c_51])).

cnf(c_69,plain,
    ( k8_relat_1(X0_35,k8_relat_1(X1_35,sK2)) = k8_relat_1(k3_xboole_0(X0_35,X1_35),sK2) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_85,plain,
    ( k8_relat_1(X0_35,k8_relat_1(X1_35,sK2)) = k8_relat_1(k3_xboole_0(X1_35,X0_35),sK2) ),
    inference(superposition,[status(thm)],[c_71,c_69])).

cnf(c_88,plain,
    ( k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k8_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_68,c_85])).

cnf(c_3,negated_conjecture,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_70,negated_conjecture,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_92,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_88,c_70])).

cnf(c_93,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_92])).


%------------------------------------------------------------------------------
