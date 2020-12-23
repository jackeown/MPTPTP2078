%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0769+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:05 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 (  70 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k7_relat_1(X2,X1)) = k7_relat_1(k8_relat_1(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k7_relat_1(X2,X1)) = k7_relat_1(k8_relat_1(X0,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X2,X1)) = k7_relat_1(k8_relat_1(X0,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,k7_relat_1(X1,X0)) = k2_wellord1(X1,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,k7_relat_1(X1,X0)) != k2_wellord1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,k7_relat_1(X1,X0)) != k2_wellord1(X1,X0)
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK0,k7_relat_1(sK1,sK0)) != k2_wellord1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( k8_relat_1(sK0,k7_relat_1(sK1,sK0)) != k2_wellord1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    k8_relat_1(sK0,k7_relat_1(sK1,sK0)) != k2_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_47,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_48,plain,
    ( k8_relat_1(X0,k7_relat_1(sK1,X1)) = k7_relat_1(k8_relat_1(X0,sK1),X1) ),
    inference(unflattening,[status(thm)],[c_47])).

cnf(c_60,plain,
    ( k8_relat_1(X0_35,k7_relat_1(sK1,X1_35)) = k7_relat_1(k8_relat_1(X0_35,sK1),X1_35) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_2,negated_conjecture,
    ( k8_relat_1(sK0,k7_relat_1(sK1,sK0)) != k2_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_62,negated_conjecture,
    ( k8_relat_1(sK0,k7_relat_1(sK1,sK0)) != k2_wellord1(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_74,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK1),sK0) != k2_wellord1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_60,c_62])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_41,plain,
    ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_42,plain,
    ( k7_relat_1(k8_relat_1(X0,sK1),X0) = k2_wellord1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_41])).

cnf(c_61,plain,
    ( k7_relat_1(k8_relat_1(X0_35,sK1),X0_35) = k2_wellord1(sK1,X0_35) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_75,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_74,c_61])).

cnf(c_76,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_75])).


%------------------------------------------------------------------------------
