%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0448+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:19 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of clauses        :   18 (  20 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = k1_tarski(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relat_1(X2) = k1_tarski(X1)
        & k1_relat_1(X2) = k1_tarski(X0) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relat_1(X2) = k1_tarski(X1)
        & k1_relat_1(X2) = k1_tarski(X0) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k1_tarski(X1)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1)
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f16])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_tarski(X0)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0)
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f15])).

fof(f5,conjecture,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,
    ( ? [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) != k2_tarski(X0,X1)
   => k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f18,plain,(
    k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,plain,(
    k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f18,f17])).

cnf(c_1,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_64,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_132,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_65,plain,
    ( ~ v1_relat_1(X0_37)
    | k2_xboole_0(k1_relat_1(X0_37),k2_relat_1(X0_37)) = k3_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_131,plain,
    ( k2_xboole_0(k1_relat_1(X0_37),k2_relat_1(X0_37)) = k3_relat_1(X0_37)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_229,plain,
    ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))),k2_relat_1(k1_tarski(k4_tarski(X0_38,X1_38)))) = k3_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) ),
    inference(superposition,[status(thm)],[c_132,c_131])).

cnf(c_2,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_30,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_1])).

cnf(c_61,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) = k1_tarski(X1_38) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3,plain,
    ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
    | k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_26,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_1])).

cnf(c_62,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) = k1_tarski(X0_38) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_230,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_tarski(X1_38)) = k3_relat_1(k1_tarski(k4_tarski(X0_38,X1_38))) ),
    inference(light_normalisation,[status(thm)],[c_229,c_61,c_62])).

cnf(c_4,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_63,negated_conjecture,
    ( k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_233,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_230,c_63])).

cnf(c_303,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_233])).


%------------------------------------------------------------------------------
