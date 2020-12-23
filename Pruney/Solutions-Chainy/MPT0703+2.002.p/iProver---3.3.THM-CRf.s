%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:15 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 365 expanded)
%              Number of clauses        :   47 ( 123 expanded)
%              Number of leaves         :    9 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  166 ( 890 expanded)
%              Number of equality atoms :   69 ( 247 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_397,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_716,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_397])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_395,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1006,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_397,c_395])).

cnf(c_1965,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1006])).

cnf(c_1960,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1006])).

cnf(c_2117,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1965,c_1960])).

cnf(c_2118,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_1965,c_1006])).

cnf(c_2123,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2118,c_1965])).

cnf(c_2126,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2117,c_1965,c_2123])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_388,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_setfam_1(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_394,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1769,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_394])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2278,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_15])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_390,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1008,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_390,c_395])).

cnf(c_2292,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2278,c_1008])).

cnf(c_2324,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))) ),
    inference(superposition,[status(thm)],[c_2292,c_2278])).

cnf(c_2326,plain,
    ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0))) ),
    inference(demodulation,[status(thm)],[c_2324,c_2278])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_393,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_859,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1)))) = k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_393])).

cnf(c_5038,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_859])).

cnf(c_5856,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5038,c_15])).

cnf(c_5862,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),k1_setfam_1(k2_tarski(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_2326,c_5856])).

cnf(c_5883,plain,
    ( k1_setfam_1(k2_tarski(k2_relat_1(sK2),k1_setfam_1(k2_tarski(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)) ),
    inference(demodulation,[status(thm)],[c_5862,c_5856])).

cnf(c_5899,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5883,c_716])).

cnf(c_7056,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK2))),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2126,c_5899])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_391,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1007,plain,
    ( k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_391,c_395])).

cnf(c_7072,plain,
    ( r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7056,c_1007])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_396,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8031,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7072,c_396])).

cnf(c_20092,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_8031])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20092,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.39/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.50  
% 7.39/1.50  ------  iProver source info
% 7.39/1.50  
% 7.39/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.50  git: non_committed_changes: false
% 7.39/1.50  git: last_make_outside_of_git: false
% 7.39/1.50  
% 7.39/1.50  ------ 
% 7.39/1.50  ------ Parsing...
% 7.39/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.50  
% 7.39/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.50  ------ Proving...
% 7.39/1.50  ------ Problem Properties 
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  clauses                                 13
% 7.39/1.50  conjectures                             5
% 7.39/1.50  EPR                                     6
% 7.39/1.50  Horn                                    13
% 7.39/1.50  unary                                   8
% 7.39/1.50  binary                                  1
% 7.39/1.50  lits                                    23
% 7.39/1.50  lits eq                                 5
% 7.39/1.50  fd_pure                                 0
% 7.39/1.50  fd_pseudo                               0
% 7.39/1.50  fd_cond                                 0
% 7.39/1.50  fd_pseudo_cond                          1
% 7.39/1.50  AC symbols                              0
% 7.39/1.50  
% 7.39/1.50  ------ Input Options Time Limit: Unbounded
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  ------ 
% 7.39/1.50  Current options:
% 7.39/1.50  ------ 
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  ------ Proving...
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS status Theorem for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  fof(f5,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f30,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f5])).
% 7.39/1.50  
% 7.39/1.50  fof(f2,axiom,(
% 7.39/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f27,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f2])).
% 7.39/1.50  
% 7.39/1.50  fof(f6,axiom,(
% 7.39/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f31,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f6])).
% 7.39/1.50  
% 7.39/1.50  fof(f39,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f27,f31])).
% 7.39/1.50  
% 7.39/1.50  fof(f4,axiom,(
% 7.39/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f13,plain,(
% 7.39/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f4])).
% 7.39/1.50  
% 7.39/1.50  fof(f29,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f13])).
% 7.39/1.50  
% 7.39/1.50  fof(f40,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f29,f31])).
% 7.39/1.50  
% 7.39/1.50  fof(f9,conjecture,(
% 7.39/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f10,negated_conjecture,(
% 7.39/1.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.39/1.50    inference(negated_conjecture,[],[f9])).
% 7.39/1.50  
% 7.39/1.50  fof(f18,plain,(
% 7.39/1.50    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.39/1.50    inference(ennf_transformation,[],[f10])).
% 7.39/1.50  
% 7.39/1.50  fof(f19,plain,(
% 7.39/1.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.39/1.50    inference(flattening,[],[f18])).
% 7.39/1.50  
% 7.39/1.50  fof(f22,plain,(
% 7.39/1.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f23,plain,(
% 7.39/1.50    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.39/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).
% 7.39/1.50  
% 7.39/1.50  fof(f34,plain,(
% 7.39/1.50    v1_relat_1(sK2)),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f7,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f14,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.39/1.50    inference(ennf_transformation,[],[f7])).
% 7.39/1.50  
% 7.39/1.50  fof(f15,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.39/1.50    inference(flattening,[],[f14])).
% 7.39/1.50  
% 7.39/1.50  fof(f32,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f15])).
% 7.39/1.50  
% 7.39/1.50  fof(f41,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f32,f31,f31])).
% 7.39/1.50  
% 7.39/1.50  fof(f35,plain,(
% 7.39/1.50    v1_funct_1(sK2)),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f36,plain,(
% 7.39/1.50    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f8,axiom,(
% 7.39/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f16,plain,(
% 7.39/1.50    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.39/1.50    inference(ennf_transformation,[],[f8])).
% 7.39/1.50  
% 7.39/1.50  fof(f17,plain,(
% 7.39/1.50    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.39/1.50    inference(flattening,[],[f16])).
% 7.39/1.50  
% 7.39/1.50  fof(f33,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f17])).
% 7.39/1.50  
% 7.39/1.50  fof(f37,plain,(
% 7.39/1.50    r1_tarski(sK0,k2_relat_1(sK2))),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f3,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.39/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f11,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.39/1.50    inference(ennf_transformation,[],[f3])).
% 7.39/1.50  
% 7.39/1.50  fof(f12,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.39/1.50    inference(flattening,[],[f11])).
% 7.39/1.50  
% 7.39/1.50  fof(f28,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f12])).
% 7.39/1.50  
% 7.39/1.50  fof(f38,plain,(
% 7.39/1.50    ~r1_tarski(sK0,sK1)),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  cnf(c_6,plain,
% 7.39/1.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_3,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_397,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_716,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_6,c_397]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5,plain,
% 7.39/1.50      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.39/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_395,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 7.39/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1006,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_397,c_395]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1965,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_6,c_1006]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1960,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_6,c_1006]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2117,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_1965,c_1960]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2118,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_1965,c_1006]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2123,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,X0)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.39/1.50      inference(demodulation,[status(thm)],[c_2118,c_1965]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2126,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 7.39/1.50      inference(light_normalisation,[status(thm)],[c_2117,c_1965,c_2123]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_13,negated_conjecture,
% 7.39/1.50      ( v1_relat_1(sK2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_388,plain,
% 7.39/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_7,plain,
% 7.39/1.50      ( ~ v1_relat_1(X0)
% 7.39/1.50      | ~ v1_funct_1(X0)
% 7.39/1.50      | k1_setfam_1(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 7.39/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_394,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2)))
% 7.39/1.50      | v1_relat_1(X0) != iProver_top
% 7.39/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1769,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))
% 7.39/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_388,c_394]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_12,negated_conjecture,
% 7.39/1.50      ( v1_funct_1(sK2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_15,plain,
% 7.39/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2278,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
% 7.39/1.50      inference(global_propositional_subsumption,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_1769,c_15]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_11,negated_conjecture,
% 7.39/1.50      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_390,plain,
% 7.39/1.50      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1008,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_390,c_395]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2292,plain,
% 7.39/1.50      ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) = k10_relat_1(sK2,sK0) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_2278,c_1008]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2324,plain,
% 7.39/1.50      ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_2292,c_2278]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2326,plain,
% 7.39/1.50      ( k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK0,sK1))))) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(X0,sK0))) ),
% 7.39/1.50      inference(demodulation,[status(thm)],[c_2324,c_2278]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_8,plain,
% 7.39/1.50      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.39/1.50      | ~ v1_relat_1(X1)
% 7.39/1.50      | ~ v1_funct_1(X1)
% 7.39/1.50      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 7.39/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_393,plain,
% 7.39/1.50      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 7.39/1.50      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 7.39/1.50      | v1_relat_1(X0) != iProver_top
% 7.39/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_859,plain,
% 7.39/1.50      ( k9_relat_1(X0,k10_relat_1(X0,k1_setfam_1(k2_tarski(k2_relat_1(X0),X1)))) = k1_setfam_1(k2_tarski(k2_relat_1(X0),X1))
% 7.39/1.50      | v1_relat_1(X0) != iProver_top
% 7.39/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_397,c_393]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5038,plain,
% 7.39/1.50      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0))
% 7.39/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_388,c_859]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5856,plain,
% 7.39/1.50      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),X0)) ),
% 7.39/1.50      inference(global_propositional_subsumption,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_5038,c_15]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5862,plain,
% 7.39/1.50      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),k1_setfam_1(k2_tarski(sK0,sK1)))) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_2326,c_5856]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5883,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(k2_relat_1(sK2),k1_setfam_1(k2_tarski(sK0,sK1)))) = k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)) ),
% 7.39/1.50      inference(demodulation,[status(thm)],[c_5862,c_5856]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5899,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(k2_relat_1(sK2),sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_5883,c_716]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_7056,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK2))),k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_2126,c_5899]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_10,negated_conjecture,
% 7.39/1.50      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_391,plain,
% 7.39/1.50      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1007,plain,
% 7.39/1.50      ( k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK2))) = sK0 ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_391,c_395]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_7072,plain,
% 7.39/1.50      ( r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) = iProver_top ),
% 7.39/1.50      inference(light_normalisation,[status(thm)],[c_7056,c_1007]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4,plain,
% 7.39/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_396,plain,
% 7.39/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.39/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.39/1.50      | r1_tarski(X0,X2) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_8031,plain,
% 7.39/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),X0) != iProver_top
% 7.39/1.50      | r1_tarski(sK0,X0) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_7072,c_396]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_20092,plain,
% 7.39/1.50      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_716,c_8031]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_9,negated_conjecture,
% 7.39/1.50      ( ~ r1_tarski(sK0,sK1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_18,plain,
% 7.39/1.50      ( r1_tarski(sK0,sK1) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(contradiction,plain,
% 7.39/1.50      ( $false ),
% 7.39/1.50      inference(minisat,[status(thm)],[c_20092,c_18]) ).
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  ------                               Statistics
% 7.39/1.50  
% 7.39/1.50  ------ Selected
% 7.39/1.50  
% 7.39/1.50  total_time:                             0.584
% 7.39/1.50  
%------------------------------------------------------------------------------
