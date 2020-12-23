%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:18 EST 2020

% Result     : Theorem 39.55s
% Output     : CNFRefutation 39.55s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 213 expanded)
%              Number of clauses        :   51 (  69 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  216 ( 736 expanded)
%              Number of equality atoms :   85 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,
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

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_626,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_632,plain,
    ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1715,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_632])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4001,plain,
    ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_17])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_628,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_634,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1135,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_628,c_634])).

cnf(c_4013,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_4001,c_1135])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_629,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_636,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_635,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1533,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_635])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_631,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2868,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2)
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_631])).

cnf(c_6621,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_2868])).

cnf(c_789,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_relat_1(X2))
    | r1_tarski(X0,k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_915,plain,
    ( r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_945,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ r1_tarski(k3_xboole_0(sK0,X0),sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_946,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1240,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7979,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6621,c_15,c_14,c_12,c_945,c_946,c_1240])).

cnf(c_11640,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4013,c_7979])).

cnf(c_1277,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_631])).

cnf(c_792,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3015,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1277,c_15,c_14,c_12,c_792])).

cnf(c_11677,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_11640,c_3015])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_637,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_178394,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11677,c_637])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_639,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_638,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1306,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_639,c_638])).

cnf(c_1131,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_639,c_634])).

cnf(c_1945,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1306,c_1131])).

cnf(c_178616,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_178394,c_1945])).

cnf(c_178617,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_178616])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_178617,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 39.55/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.55/5.48  
% 39.55/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.55/5.48  
% 39.55/5.48  ------  iProver source info
% 39.55/5.48  
% 39.55/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.55/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.55/5.48  git: non_committed_changes: false
% 39.55/5.48  git: last_make_outside_of_git: false
% 39.55/5.48  
% 39.55/5.48  ------ 
% 39.55/5.48  
% 39.55/5.48  ------ Input Options
% 39.55/5.48  
% 39.55/5.48  --out_options                           all
% 39.55/5.48  --tptp_safe_out                         true
% 39.55/5.48  --problem_path                          ""
% 39.55/5.48  --include_path                          ""
% 39.55/5.48  --clausifier                            res/vclausify_rel
% 39.55/5.48  --clausifier_options                    --mode clausify
% 39.55/5.48  --stdin                                 false
% 39.55/5.48  --stats_out                             sel
% 39.55/5.48  
% 39.55/5.48  ------ General Options
% 39.55/5.48  
% 39.55/5.48  --fof                                   false
% 39.55/5.48  --time_out_real                         604.99
% 39.55/5.48  --time_out_virtual                      -1.
% 39.55/5.48  --symbol_type_check                     false
% 39.55/5.48  --clausify_out                          false
% 39.55/5.48  --sig_cnt_out                           false
% 39.55/5.48  --trig_cnt_out                          false
% 39.55/5.48  --trig_cnt_out_tolerance                1.
% 39.55/5.48  --trig_cnt_out_sk_spl                   false
% 39.55/5.48  --abstr_cl_out                          false
% 39.55/5.48  
% 39.55/5.48  ------ Global Options
% 39.55/5.48  
% 39.55/5.48  --schedule                              none
% 39.55/5.48  --add_important_lit                     false
% 39.55/5.48  --prop_solver_per_cl                    1000
% 39.55/5.48  --min_unsat_core                        false
% 39.55/5.48  --soft_assumptions                      false
% 39.55/5.48  --soft_lemma_size                       3
% 39.55/5.48  --prop_impl_unit_size                   0
% 39.55/5.48  --prop_impl_unit                        []
% 39.55/5.48  --share_sel_clauses                     true
% 39.55/5.48  --reset_solvers                         false
% 39.55/5.48  --bc_imp_inh                            [conj_cone]
% 39.55/5.48  --conj_cone_tolerance                   3.
% 39.55/5.48  --extra_neg_conj                        none
% 39.55/5.48  --large_theory_mode                     true
% 39.55/5.48  --prolific_symb_bound                   200
% 39.55/5.48  --lt_threshold                          2000
% 39.55/5.48  --clause_weak_htbl                      true
% 39.55/5.48  --gc_record_bc_elim                     false
% 39.55/5.48  
% 39.55/5.48  ------ Preprocessing Options
% 39.55/5.48  
% 39.55/5.48  --preprocessing_flag                    true
% 39.55/5.48  --time_out_prep_mult                    0.1
% 39.55/5.48  --splitting_mode                        input
% 39.55/5.48  --splitting_grd                         true
% 39.55/5.48  --splitting_cvd                         false
% 39.55/5.48  --splitting_cvd_svl                     false
% 39.55/5.48  --splitting_nvd                         32
% 39.55/5.48  --sub_typing                            true
% 39.55/5.48  --prep_gs_sim                           false
% 39.55/5.48  --prep_unflatten                        true
% 39.55/5.48  --prep_res_sim                          true
% 39.55/5.48  --prep_upred                            true
% 39.55/5.48  --prep_sem_filter                       exhaustive
% 39.55/5.48  --prep_sem_filter_out                   false
% 39.55/5.48  --pred_elim                             false
% 39.55/5.48  --res_sim_input                         true
% 39.55/5.48  --eq_ax_congr_red                       true
% 39.55/5.48  --pure_diseq_elim                       true
% 39.55/5.48  --brand_transform                       false
% 39.55/5.48  --non_eq_to_eq                          false
% 39.55/5.48  --prep_def_merge                        true
% 39.55/5.48  --prep_def_merge_prop_impl              false
% 39.55/5.48  --prep_def_merge_mbd                    true
% 39.55/5.48  --prep_def_merge_tr_red                 false
% 39.55/5.48  --prep_def_merge_tr_cl                  false
% 39.55/5.48  --smt_preprocessing                     true
% 39.55/5.48  --smt_ac_axioms                         fast
% 39.55/5.48  --preprocessed_out                      false
% 39.55/5.48  --preprocessed_stats                    false
% 39.55/5.48  
% 39.55/5.48  ------ Abstraction refinement Options
% 39.55/5.48  
% 39.55/5.48  --abstr_ref                             []
% 39.55/5.48  --abstr_ref_prep                        false
% 39.55/5.48  --abstr_ref_until_sat                   false
% 39.55/5.48  --abstr_ref_sig_restrict                funpre
% 39.55/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.55/5.48  --abstr_ref_under                       []
% 39.55/5.48  
% 39.55/5.48  ------ SAT Options
% 39.55/5.48  
% 39.55/5.48  --sat_mode                              false
% 39.55/5.48  --sat_fm_restart_options                ""
% 39.55/5.48  --sat_gr_def                            false
% 39.55/5.48  --sat_epr_types                         true
% 39.55/5.48  --sat_non_cyclic_types                  false
% 39.55/5.48  --sat_finite_models                     false
% 39.55/5.48  --sat_fm_lemmas                         false
% 39.55/5.48  --sat_fm_prep                           false
% 39.55/5.48  --sat_fm_uc_incr                        true
% 39.55/5.48  --sat_out_model                         small
% 39.55/5.48  --sat_out_clauses                       false
% 39.55/5.48  
% 39.55/5.48  ------ QBF Options
% 39.55/5.48  
% 39.55/5.48  --qbf_mode                              false
% 39.55/5.48  --qbf_elim_univ                         false
% 39.55/5.48  --qbf_dom_inst                          none
% 39.55/5.48  --qbf_dom_pre_inst                      false
% 39.55/5.48  --qbf_sk_in                             false
% 39.55/5.48  --qbf_pred_elim                         true
% 39.55/5.48  --qbf_split                             512
% 39.55/5.48  
% 39.55/5.48  ------ BMC1 Options
% 39.55/5.48  
% 39.55/5.48  --bmc1_incremental                      false
% 39.55/5.48  --bmc1_axioms                           reachable_all
% 39.55/5.48  --bmc1_min_bound                        0
% 39.55/5.48  --bmc1_max_bound                        -1
% 39.55/5.48  --bmc1_max_bound_default                -1
% 39.55/5.48  --bmc1_symbol_reachability              true
% 39.55/5.48  --bmc1_property_lemmas                  false
% 39.55/5.48  --bmc1_k_induction                      false
% 39.55/5.48  --bmc1_non_equiv_states                 false
% 39.55/5.48  --bmc1_deadlock                         false
% 39.55/5.48  --bmc1_ucm                              false
% 39.55/5.48  --bmc1_add_unsat_core                   none
% 39.55/5.48  --bmc1_unsat_core_children              false
% 39.55/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.55/5.48  --bmc1_out_stat                         full
% 39.55/5.48  --bmc1_ground_init                      false
% 39.55/5.48  --bmc1_pre_inst_next_state              false
% 39.55/5.48  --bmc1_pre_inst_state                   false
% 39.55/5.48  --bmc1_pre_inst_reach_state             false
% 39.55/5.48  --bmc1_out_unsat_core                   false
% 39.55/5.48  --bmc1_aig_witness_out                  false
% 39.55/5.48  --bmc1_verbose                          false
% 39.55/5.48  --bmc1_dump_clauses_tptp                false
% 39.55/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.55/5.48  --bmc1_dump_file                        -
% 39.55/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.55/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.55/5.48  --bmc1_ucm_extend_mode                  1
% 39.55/5.48  --bmc1_ucm_init_mode                    2
% 39.55/5.48  --bmc1_ucm_cone_mode                    none
% 39.55/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.55/5.48  --bmc1_ucm_relax_model                  4
% 39.55/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.55/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.55/5.48  --bmc1_ucm_layered_model                none
% 39.55/5.48  --bmc1_ucm_max_lemma_size               10
% 39.55/5.48  
% 39.55/5.48  ------ AIG Options
% 39.55/5.48  
% 39.55/5.48  --aig_mode                              false
% 39.55/5.48  
% 39.55/5.48  ------ Instantiation Options
% 39.55/5.48  
% 39.55/5.48  --instantiation_flag                    true
% 39.55/5.48  --inst_sos_flag                         false
% 39.55/5.48  --inst_sos_phase                        true
% 39.55/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.55/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.55/5.48  --inst_lit_sel_side                     num_symb
% 39.55/5.48  --inst_solver_per_active                1400
% 39.55/5.48  --inst_solver_calls_frac                1.
% 39.55/5.48  --inst_passive_queue_type               priority_queues
% 39.55/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.55/5.48  --inst_passive_queues_freq              [25;2]
% 39.55/5.48  --inst_dismatching                      true
% 39.55/5.48  --inst_eager_unprocessed_to_passive     true
% 39.55/5.48  --inst_prop_sim_given                   true
% 39.55/5.48  --inst_prop_sim_new                     false
% 39.55/5.48  --inst_subs_new                         false
% 39.55/5.48  --inst_eq_res_simp                      false
% 39.55/5.48  --inst_subs_given                       false
% 39.55/5.48  --inst_orphan_elimination               true
% 39.55/5.48  --inst_learning_loop_flag               true
% 39.55/5.48  --inst_learning_start                   3000
% 39.55/5.48  --inst_learning_factor                  2
% 39.55/5.48  --inst_start_prop_sim_after_learn       3
% 39.55/5.48  --inst_sel_renew                        solver
% 39.55/5.48  --inst_lit_activity_flag                true
% 39.55/5.48  --inst_restr_to_given                   false
% 39.55/5.48  --inst_activity_threshold               500
% 39.55/5.48  --inst_out_proof                        true
% 39.55/5.48  
% 39.55/5.48  ------ Resolution Options
% 39.55/5.48  
% 39.55/5.48  --resolution_flag                       true
% 39.55/5.48  --res_lit_sel                           adaptive
% 39.55/5.48  --res_lit_sel_side                      none
% 39.55/5.48  --res_ordering                          kbo
% 39.55/5.48  --res_to_prop_solver                    active
% 39.55/5.48  --res_prop_simpl_new                    false
% 39.55/5.48  --res_prop_simpl_given                  true
% 39.55/5.48  --res_passive_queue_type                priority_queues
% 39.55/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.55/5.48  --res_passive_queues_freq               [15;5]
% 39.55/5.48  --res_forward_subs                      full
% 39.55/5.48  --res_backward_subs                     full
% 39.55/5.48  --res_forward_subs_resolution           true
% 39.55/5.48  --res_backward_subs_resolution          true
% 39.55/5.48  --res_orphan_elimination                true
% 39.55/5.48  --res_time_limit                        2.
% 39.55/5.48  --res_out_proof                         true
% 39.55/5.48  
% 39.55/5.48  ------ Superposition Options
% 39.55/5.48  
% 39.55/5.48  --superposition_flag                    true
% 39.55/5.48  --sup_passive_queue_type                priority_queues
% 39.55/5.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.55/5.48  --sup_passive_queues_freq               [1;4]
% 39.55/5.48  --demod_completeness_check              fast
% 39.55/5.48  --demod_use_ground                      true
% 39.55/5.48  --sup_to_prop_solver                    passive
% 39.55/5.48  --sup_prop_simpl_new                    true
% 39.55/5.48  --sup_prop_simpl_given                  true
% 39.55/5.48  --sup_fun_splitting                     false
% 39.55/5.48  --sup_smt_interval                      50000
% 39.55/5.48  
% 39.55/5.48  ------ Superposition Simplification Setup
% 39.55/5.48  
% 39.55/5.48  --sup_indices_passive                   []
% 39.55/5.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.55/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_full_bw                           [BwDemod]
% 39.55/5.48  --sup_immed_triv                        [TrivRules]
% 39.55/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.55/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_immed_bw_main                     []
% 39.55/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.55/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.55/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.55/5.48  
% 39.55/5.48  ------ Combination Options
% 39.55/5.48  
% 39.55/5.48  --comb_res_mult                         3
% 39.55/5.48  --comb_sup_mult                         2
% 39.55/5.48  --comb_inst_mult                        10
% 39.55/5.48  
% 39.55/5.48  ------ Debug Options
% 39.55/5.48  
% 39.55/5.48  --dbg_backtrace                         false
% 39.55/5.48  --dbg_dump_prop_clauses                 false
% 39.55/5.48  --dbg_dump_prop_clauses_file            -
% 39.55/5.48  --dbg_out_stat                          false
% 39.55/5.48  ------ Parsing...
% 39.55/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.55/5.48  
% 39.55/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.55/5.48  
% 39.55/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.55/5.48  
% 39.55/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.55/5.48  ------ Proving...
% 39.55/5.48  ------ Problem Properties 
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  clauses                                 15
% 39.55/5.48  conjectures                             5
% 39.55/5.48  EPR                                     6
% 39.55/5.48  Horn                                    15
% 39.55/5.48  unary                                   8
% 39.55/5.48  binary                                  3
% 39.55/5.48  lits                                    27
% 39.55/5.48  lits eq                                 6
% 39.55/5.48  fd_pure                                 0
% 39.55/5.48  fd_pseudo                               0
% 39.55/5.48  fd_cond                                 0
% 39.55/5.48  fd_pseudo_cond                          1
% 39.55/5.48  AC symbols                              0
% 39.55/5.48  
% 39.55/5.48  ------ Input Options Time Limit: Unbounded
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  ------ 
% 39.55/5.48  Current options:
% 39.55/5.48  ------ 
% 39.55/5.48  
% 39.55/5.48  ------ Input Options
% 39.55/5.48  
% 39.55/5.48  --out_options                           all
% 39.55/5.48  --tptp_safe_out                         true
% 39.55/5.48  --problem_path                          ""
% 39.55/5.48  --include_path                          ""
% 39.55/5.48  --clausifier                            res/vclausify_rel
% 39.55/5.48  --clausifier_options                    --mode clausify
% 39.55/5.48  --stdin                                 false
% 39.55/5.48  --stats_out                             sel
% 39.55/5.48  
% 39.55/5.48  ------ General Options
% 39.55/5.48  
% 39.55/5.48  --fof                                   false
% 39.55/5.48  --time_out_real                         604.99
% 39.55/5.48  --time_out_virtual                      -1.
% 39.55/5.48  --symbol_type_check                     false
% 39.55/5.48  --clausify_out                          false
% 39.55/5.48  --sig_cnt_out                           false
% 39.55/5.48  --trig_cnt_out                          false
% 39.55/5.48  --trig_cnt_out_tolerance                1.
% 39.55/5.48  --trig_cnt_out_sk_spl                   false
% 39.55/5.48  --abstr_cl_out                          false
% 39.55/5.48  
% 39.55/5.48  ------ Global Options
% 39.55/5.48  
% 39.55/5.48  --schedule                              none
% 39.55/5.48  --add_important_lit                     false
% 39.55/5.48  --prop_solver_per_cl                    1000
% 39.55/5.48  --min_unsat_core                        false
% 39.55/5.48  --soft_assumptions                      false
% 39.55/5.48  --soft_lemma_size                       3
% 39.55/5.48  --prop_impl_unit_size                   0
% 39.55/5.48  --prop_impl_unit                        []
% 39.55/5.48  --share_sel_clauses                     true
% 39.55/5.48  --reset_solvers                         false
% 39.55/5.48  --bc_imp_inh                            [conj_cone]
% 39.55/5.48  --conj_cone_tolerance                   3.
% 39.55/5.48  --extra_neg_conj                        none
% 39.55/5.48  --large_theory_mode                     true
% 39.55/5.48  --prolific_symb_bound                   200
% 39.55/5.48  --lt_threshold                          2000
% 39.55/5.48  --clause_weak_htbl                      true
% 39.55/5.48  --gc_record_bc_elim                     false
% 39.55/5.48  
% 39.55/5.48  ------ Preprocessing Options
% 39.55/5.48  
% 39.55/5.48  --preprocessing_flag                    true
% 39.55/5.48  --time_out_prep_mult                    0.1
% 39.55/5.48  --splitting_mode                        input
% 39.55/5.48  --splitting_grd                         true
% 39.55/5.48  --splitting_cvd                         false
% 39.55/5.48  --splitting_cvd_svl                     false
% 39.55/5.48  --splitting_nvd                         32
% 39.55/5.48  --sub_typing                            true
% 39.55/5.48  --prep_gs_sim                           false
% 39.55/5.48  --prep_unflatten                        true
% 39.55/5.48  --prep_res_sim                          true
% 39.55/5.48  --prep_upred                            true
% 39.55/5.48  --prep_sem_filter                       exhaustive
% 39.55/5.48  --prep_sem_filter_out                   false
% 39.55/5.48  --pred_elim                             false
% 39.55/5.48  --res_sim_input                         true
% 39.55/5.48  --eq_ax_congr_red                       true
% 39.55/5.48  --pure_diseq_elim                       true
% 39.55/5.48  --brand_transform                       false
% 39.55/5.48  --non_eq_to_eq                          false
% 39.55/5.48  --prep_def_merge                        true
% 39.55/5.48  --prep_def_merge_prop_impl              false
% 39.55/5.48  --prep_def_merge_mbd                    true
% 39.55/5.48  --prep_def_merge_tr_red                 false
% 39.55/5.48  --prep_def_merge_tr_cl                  false
% 39.55/5.48  --smt_preprocessing                     true
% 39.55/5.48  --smt_ac_axioms                         fast
% 39.55/5.48  --preprocessed_out                      false
% 39.55/5.48  --preprocessed_stats                    false
% 39.55/5.48  
% 39.55/5.48  ------ Abstraction refinement Options
% 39.55/5.48  
% 39.55/5.48  --abstr_ref                             []
% 39.55/5.48  --abstr_ref_prep                        false
% 39.55/5.48  --abstr_ref_until_sat                   false
% 39.55/5.48  --abstr_ref_sig_restrict                funpre
% 39.55/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.55/5.48  --abstr_ref_under                       []
% 39.55/5.48  
% 39.55/5.48  ------ SAT Options
% 39.55/5.48  
% 39.55/5.48  --sat_mode                              false
% 39.55/5.48  --sat_fm_restart_options                ""
% 39.55/5.48  --sat_gr_def                            false
% 39.55/5.48  --sat_epr_types                         true
% 39.55/5.48  --sat_non_cyclic_types                  false
% 39.55/5.48  --sat_finite_models                     false
% 39.55/5.48  --sat_fm_lemmas                         false
% 39.55/5.48  --sat_fm_prep                           false
% 39.55/5.48  --sat_fm_uc_incr                        true
% 39.55/5.48  --sat_out_model                         small
% 39.55/5.48  --sat_out_clauses                       false
% 39.55/5.48  
% 39.55/5.48  ------ QBF Options
% 39.55/5.48  
% 39.55/5.48  --qbf_mode                              false
% 39.55/5.48  --qbf_elim_univ                         false
% 39.55/5.48  --qbf_dom_inst                          none
% 39.55/5.48  --qbf_dom_pre_inst                      false
% 39.55/5.48  --qbf_sk_in                             false
% 39.55/5.48  --qbf_pred_elim                         true
% 39.55/5.48  --qbf_split                             512
% 39.55/5.48  
% 39.55/5.48  ------ BMC1 Options
% 39.55/5.48  
% 39.55/5.48  --bmc1_incremental                      false
% 39.55/5.48  --bmc1_axioms                           reachable_all
% 39.55/5.48  --bmc1_min_bound                        0
% 39.55/5.48  --bmc1_max_bound                        -1
% 39.55/5.48  --bmc1_max_bound_default                -1
% 39.55/5.48  --bmc1_symbol_reachability              true
% 39.55/5.48  --bmc1_property_lemmas                  false
% 39.55/5.48  --bmc1_k_induction                      false
% 39.55/5.48  --bmc1_non_equiv_states                 false
% 39.55/5.48  --bmc1_deadlock                         false
% 39.55/5.48  --bmc1_ucm                              false
% 39.55/5.48  --bmc1_add_unsat_core                   none
% 39.55/5.48  --bmc1_unsat_core_children              false
% 39.55/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.55/5.48  --bmc1_out_stat                         full
% 39.55/5.48  --bmc1_ground_init                      false
% 39.55/5.48  --bmc1_pre_inst_next_state              false
% 39.55/5.48  --bmc1_pre_inst_state                   false
% 39.55/5.48  --bmc1_pre_inst_reach_state             false
% 39.55/5.48  --bmc1_out_unsat_core                   false
% 39.55/5.48  --bmc1_aig_witness_out                  false
% 39.55/5.48  --bmc1_verbose                          false
% 39.55/5.48  --bmc1_dump_clauses_tptp                false
% 39.55/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.55/5.48  --bmc1_dump_file                        -
% 39.55/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.55/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.55/5.48  --bmc1_ucm_extend_mode                  1
% 39.55/5.48  --bmc1_ucm_init_mode                    2
% 39.55/5.48  --bmc1_ucm_cone_mode                    none
% 39.55/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.55/5.48  --bmc1_ucm_relax_model                  4
% 39.55/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.55/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.55/5.48  --bmc1_ucm_layered_model                none
% 39.55/5.48  --bmc1_ucm_max_lemma_size               10
% 39.55/5.48  
% 39.55/5.48  ------ AIG Options
% 39.55/5.48  
% 39.55/5.48  --aig_mode                              false
% 39.55/5.48  
% 39.55/5.48  ------ Instantiation Options
% 39.55/5.48  
% 39.55/5.48  --instantiation_flag                    true
% 39.55/5.48  --inst_sos_flag                         false
% 39.55/5.48  --inst_sos_phase                        true
% 39.55/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.55/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.55/5.48  --inst_lit_sel_side                     num_symb
% 39.55/5.48  --inst_solver_per_active                1400
% 39.55/5.48  --inst_solver_calls_frac                1.
% 39.55/5.48  --inst_passive_queue_type               priority_queues
% 39.55/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.55/5.48  --inst_passive_queues_freq              [25;2]
% 39.55/5.48  --inst_dismatching                      true
% 39.55/5.48  --inst_eager_unprocessed_to_passive     true
% 39.55/5.48  --inst_prop_sim_given                   true
% 39.55/5.48  --inst_prop_sim_new                     false
% 39.55/5.48  --inst_subs_new                         false
% 39.55/5.48  --inst_eq_res_simp                      false
% 39.55/5.48  --inst_subs_given                       false
% 39.55/5.48  --inst_orphan_elimination               true
% 39.55/5.48  --inst_learning_loop_flag               true
% 39.55/5.48  --inst_learning_start                   3000
% 39.55/5.48  --inst_learning_factor                  2
% 39.55/5.48  --inst_start_prop_sim_after_learn       3
% 39.55/5.48  --inst_sel_renew                        solver
% 39.55/5.48  --inst_lit_activity_flag                true
% 39.55/5.48  --inst_restr_to_given                   false
% 39.55/5.48  --inst_activity_threshold               500
% 39.55/5.48  --inst_out_proof                        true
% 39.55/5.48  
% 39.55/5.48  ------ Resolution Options
% 39.55/5.48  
% 39.55/5.48  --resolution_flag                       true
% 39.55/5.48  --res_lit_sel                           adaptive
% 39.55/5.48  --res_lit_sel_side                      none
% 39.55/5.48  --res_ordering                          kbo
% 39.55/5.48  --res_to_prop_solver                    active
% 39.55/5.48  --res_prop_simpl_new                    false
% 39.55/5.48  --res_prop_simpl_given                  true
% 39.55/5.48  --res_passive_queue_type                priority_queues
% 39.55/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.55/5.48  --res_passive_queues_freq               [15;5]
% 39.55/5.48  --res_forward_subs                      full
% 39.55/5.48  --res_backward_subs                     full
% 39.55/5.48  --res_forward_subs_resolution           true
% 39.55/5.48  --res_backward_subs_resolution          true
% 39.55/5.48  --res_orphan_elimination                true
% 39.55/5.48  --res_time_limit                        2.
% 39.55/5.48  --res_out_proof                         true
% 39.55/5.48  
% 39.55/5.48  ------ Superposition Options
% 39.55/5.48  
% 39.55/5.48  --superposition_flag                    true
% 39.55/5.48  --sup_passive_queue_type                priority_queues
% 39.55/5.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.55/5.48  --sup_passive_queues_freq               [1;4]
% 39.55/5.48  --demod_completeness_check              fast
% 39.55/5.48  --demod_use_ground                      true
% 39.55/5.48  --sup_to_prop_solver                    passive
% 39.55/5.48  --sup_prop_simpl_new                    true
% 39.55/5.48  --sup_prop_simpl_given                  true
% 39.55/5.48  --sup_fun_splitting                     false
% 39.55/5.48  --sup_smt_interval                      50000
% 39.55/5.48  
% 39.55/5.48  ------ Superposition Simplification Setup
% 39.55/5.48  
% 39.55/5.48  --sup_indices_passive                   []
% 39.55/5.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.55/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.55/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_full_bw                           [BwDemod]
% 39.55/5.48  --sup_immed_triv                        [TrivRules]
% 39.55/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.55/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_immed_bw_main                     []
% 39.55/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.55/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.55/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.55/5.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.55/5.48  
% 39.55/5.48  ------ Combination Options
% 39.55/5.48  
% 39.55/5.48  --comb_res_mult                         3
% 39.55/5.48  --comb_sup_mult                         2
% 39.55/5.48  --comb_inst_mult                        10
% 39.55/5.48  
% 39.55/5.48  ------ Debug Options
% 39.55/5.48  
% 39.55/5.48  --dbg_backtrace                         false
% 39.55/5.48  --dbg_dump_prop_clauses                 false
% 39.55/5.48  --dbg_dump_prop_clauses_file            -
% 39.55/5.48  --dbg_out_stat                          false
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  ------ Proving...
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  % SZS status Theorem for theBenchmark.p
% 39.55/5.48  
% 39.55/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.55/5.48  
% 39.55/5.48  fof(f10,conjecture,(
% 39.55/5.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f11,negated_conjecture,(
% 39.55/5.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 39.55/5.48    inference(negated_conjecture,[],[f10])).
% 39.55/5.48  
% 39.55/5.48  fof(f19,plain,(
% 39.55/5.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 39.55/5.48    inference(ennf_transformation,[],[f11])).
% 39.55/5.48  
% 39.55/5.48  fof(f20,plain,(
% 39.55/5.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 39.55/5.48    inference(flattening,[],[f19])).
% 39.55/5.48  
% 39.55/5.48  fof(f24,plain,(
% 39.55/5.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 39.55/5.48    introduced(choice_axiom,[])).
% 39.55/5.48  
% 39.55/5.48  fof(f25,plain,(
% 39.55/5.48    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 39.55/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 39.55/5.48  
% 39.55/5.48  fof(f38,plain,(
% 39.55/5.48    v1_relat_1(sK2)),
% 39.55/5.48    inference(cnf_transformation,[],[f25])).
% 39.55/5.48  
% 39.55/5.48  fof(f8,axiom,(
% 39.55/5.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f15,plain,(
% 39.55/5.48    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 39.55/5.48    inference(ennf_transformation,[],[f8])).
% 39.55/5.48  
% 39.55/5.48  fof(f16,plain,(
% 39.55/5.48    ! [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.55/5.48    inference(flattening,[],[f15])).
% 39.55/5.48  
% 39.55/5.48  fof(f36,plain,(
% 39.55/5.48    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f16])).
% 39.55/5.48  
% 39.55/5.48  fof(f39,plain,(
% 39.55/5.48    v1_funct_1(sK2)),
% 39.55/5.48    inference(cnf_transformation,[],[f25])).
% 39.55/5.48  
% 39.55/5.48  fof(f40,plain,(
% 39.55/5.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 39.55/5.48    inference(cnf_transformation,[],[f25])).
% 39.55/5.48  
% 39.55/5.48  fof(f6,axiom,(
% 39.55/5.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f14,plain,(
% 39.55/5.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.55/5.48    inference(ennf_transformation,[],[f6])).
% 39.55/5.48  
% 39.55/5.48  fof(f34,plain,(
% 39.55/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f14])).
% 39.55/5.48  
% 39.55/5.48  fof(f41,plain,(
% 39.55/5.48    r1_tarski(sK0,k2_relat_1(sK2))),
% 39.55/5.48    inference(cnf_transformation,[],[f25])).
% 39.55/5.48  
% 39.55/5.48  fof(f4,axiom,(
% 39.55/5.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f32,plain,(
% 39.55/5.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f4])).
% 39.55/5.48  
% 39.55/5.48  fof(f5,axiom,(
% 39.55/5.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f12,plain,(
% 39.55/5.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.55/5.48    inference(ennf_transformation,[],[f5])).
% 39.55/5.48  
% 39.55/5.48  fof(f13,plain,(
% 39.55/5.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 39.55/5.48    inference(flattening,[],[f12])).
% 39.55/5.48  
% 39.55/5.48  fof(f33,plain,(
% 39.55/5.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f13])).
% 39.55/5.48  
% 39.55/5.48  fof(f9,axiom,(
% 39.55/5.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f17,plain,(
% 39.55/5.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 39.55/5.48    inference(ennf_transformation,[],[f9])).
% 39.55/5.48  
% 39.55/5.48  fof(f18,plain,(
% 39.55/5.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 39.55/5.48    inference(flattening,[],[f17])).
% 39.55/5.48  
% 39.55/5.48  fof(f37,plain,(
% 39.55/5.48    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f18])).
% 39.55/5.48  
% 39.55/5.48  fof(f2,axiom,(
% 39.55/5.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f23,plain,(
% 39.55/5.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 39.55/5.48    inference(nnf_transformation,[],[f2])).
% 39.55/5.48  
% 39.55/5.48  fof(f29,plain,(
% 39.55/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.55/5.48    inference(cnf_transformation,[],[f23])).
% 39.55/5.48  
% 39.55/5.48  fof(f3,axiom,(
% 39.55/5.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f31,plain,(
% 39.55/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.55/5.48    inference(cnf_transformation,[],[f3])).
% 39.55/5.48  
% 39.55/5.48  fof(f44,plain,(
% 39.55/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.55/5.48    inference(definition_unfolding,[],[f29,f31])).
% 39.55/5.48  
% 39.55/5.48  fof(f1,axiom,(
% 39.55/5.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.55/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.55/5.48  
% 39.55/5.48  fof(f21,plain,(
% 39.55/5.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.55/5.48    inference(nnf_transformation,[],[f1])).
% 39.55/5.48  
% 39.55/5.48  fof(f22,plain,(
% 39.55/5.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.55/5.48    inference(flattening,[],[f21])).
% 39.55/5.48  
% 39.55/5.48  fof(f26,plain,(
% 39.55/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.55/5.48    inference(cnf_transformation,[],[f22])).
% 39.55/5.48  
% 39.55/5.48  fof(f46,plain,(
% 39.55/5.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.55/5.48    inference(equality_resolution,[],[f26])).
% 39.55/5.48  
% 39.55/5.48  fof(f30,plain,(
% 39.55/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 39.55/5.48    inference(cnf_transformation,[],[f23])).
% 39.55/5.48  
% 39.55/5.48  fof(f43,plain,(
% 39.55/5.48    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 39.55/5.48    inference(definition_unfolding,[],[f30,f31])).
% 39.55/5.48  
% 39.55/5.48  fof(f42,plain,(
% 39.55/5.48    ~r1_tarski(sK0,sK1)),
% 39.55/5.48    inference(cnf_transformation,[],[f25])).
% 39.55/5.48  
% 39.55/5.48  cnf(c_15,negated_conjecture,
% 39.55/5.48      ( v1_relat_1(sK2) ),
% 39.55/5.48      inference(cnf_transformation,[],[f38]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_626,plain,
% 39.55/5.48      ( v1_relat_1(sK2) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_9,plain,
% 39.55/5.48      ( ~ v1_relat_1(X0)
% 39.55/5.48      | ~ v1_funct_1(X0)
% 39.55/5.48      | k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 39.55/5.48      inference(cnf_transformation,[],[f36]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_632,plain,
% 39.55/5.48      ( k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k3_xboole_0(X1,X2))
% 39.55/5.48      | v1_relat_1(X0) != iProver_top
% 39.55/5.48      | v1_funct_1(X0) != iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1715,plain,
% 39.55/5.48      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1))
% 39.55/5.48      | v1_funct_1(sK2) != iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_626,c_632]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_14,negated_conjecture,
% 39.55/5.48      ( v1_funct_1(sK2) ),
% 39.55/5.48      inference(cnf_transformation,[],[f39]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_17,plain,
% 39.55/5.48      ( v1_funct_1(sK2) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_4001,plain,
% 39.55/5.48      ( k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k3_xboole_0(X0,X1)) ),
% 39.55/5.48      inference(global_propositional_subsumption,
% 39.55/5.48                [status(thm)],
% 39.55/5.48                [c_1715,c_17]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_13,negated_conjecture,
% 39.55/5.48      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 39.55/5.48      inference(cnf_transformation,[],[f40]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_628,plain,
% 39.55/5.48      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_7,plain,
% 39.55/5.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.55/5.48      inference(cnf_transformation,[],[f34]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_634,plain,
% 39.55/5.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1135,plain,
% 39.55/5.48      ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_628,c_634]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_4013,plain,
% 39.55/5.48      ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_4001,c_1135]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_12,negated_conjecture,
% 39.55/5.48      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 39.55/5.48      inference(cnf_transformation,[],[f41]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_629,plain,
% 39.55/5.48      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_5,plain,
% 39.55/5.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 39.55/5.48      inference(cnf_transformation,[],[f32]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_636,plain,
% 39.55/5.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_6,plain,
% 39.55/5.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 39.55/5.48      inference(cnf_transformation,[],[f33]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_635,plain,
% 39.55/5.48      ( r1_tarski(X0,X1) != iProver_top
% 39.55/5.48      | r1_tarski(X1,X2) != iProver_top
% 39.55/5.48      | r1_tarski(X0,X2) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1533,plain,
% 39.55/5.48      ( r1_tarski(X0,X1) != iProver_top
% 39.55/5.48      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_636,c_635]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_10,plain,
% 39.55/5.48      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 39.55/5.48      | ~ v1_relat_1(X1)
% 39.55/5.48      | ~ v1_funct_1(X1)
% 39.55/5.48      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 39.55/5.48      inference(cnf_transformation,[],[f37]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_631,plain,
% 39.55/5.48      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 39.55/5.48      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 39.55/5.48      | v1_relat_1(X0) != iProver_top
% 39.55/5.48      | v1_funct_1(X0) != iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_2868,plain,
% 39.55/5.48      ( k9_relat_1(X0,k10_relat_1(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2)
% 39.55/5.48      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 39.55/5.48      | v1_relat_1(X0) != iProver_top
% 39.55/5.48      | v1_funct_1(X0) != iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_1533,c_631]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_6621,plain,
% 39.55/5.48      ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0)
% 39.55/5.48      | v1_relat_1(sK2) != iProver_top
% 39.55/5.48      | v1_funct_1(sK2) != iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_629,c_2868]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_789,plain,
% 39.55/5.48      ( ~ r1_tarski(X0,X1)
% 39.55/5.48      | ~ r1_tarski(X1,k2_relat_1(X2))
% 39.55/5.48      | r1_tarski(X0,k2_relat_1(X2)) ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_6]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_915,plain,
% 39.55/5.48      ( r1_tarski(X0,k2_relat_1(sK2))
% 39.55/5.48      | ~ r1_tarski(X0,sK0)
% 39.55/5.48      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_789]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_945,plain,
% 39.55/5.48      ( r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2))
% 39.55/5.48      | ~ r1_tarski(k3_xboole_0(sK0,X0),sK0)
% 39.55/5.48      | ~ r1_tarski(sK0,k2_relat_1(sK2)) ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_915]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_946,plain,
% 39.55/5.48      ( r1_tarski(k3_xboole_0(sK0,X0),sK0) ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_5]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1240,plain,
% 39.55/5.48      ( ~ r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK2))
% 39.55/5.48      | ~ v1_relat_1(sK2)
% 39.55/5.48      | ~ v1_funct_1(sK2)
% 39.55/5.48      | k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_10]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_7979,plain,
% 39.55/5.48      ( k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) = k3_xboole_0(sK0,X0) ),
% 39.55/5.48      inference(global_propositional_subsumption,
% 39.55/5.48                [status(thm)],
% 39.55/5.48                [c_6621,c_15,c_14,c_12,c_945,c_946,c_1240]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_11640,plain,
% 39.55/5.48      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(sK0,sK1) ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_4013,c_7979]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1277,plain,
% 39.55/5.48      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0
% 39.55/5.48      | v1_relat_1(sK2) != iProver_top
% 39.55/5.48      | v1_funct_1(sK2) != iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_629,c_631]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_792,plain,
% 39.55/5.48      ( ~ r1_tarski(sK0,k2_relat_1(sK2))
% 39.55/5.48      | ~ v1_relat_1(sK2)
% 39.55/5.48      | ~ v1_funct_1(sK2)
% 39.55/5.48      | k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 39.55/5.48      inference(instantiation,[status(thm)],[c_10]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_3015,plain,
% 39.55/5.48      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 39.55/5.48      inference(global_propositional_subsumption,
% 39.55/5.48                [status(thm)],
% 39.55/5.48                [c_1277,c_15,c_14,c_12,c_792]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_11677,plain,
% 39.55/5.48      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 39.55/5.48      inference(light_normalisation,[status(thm)],[c_11640,c_3015]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_4,plain,
% 39.55/5.48      ( r1_tarski(X0,X1)
% 39.55/5.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.55/5.48      inference(cnf_transformation,[],[f44]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_637,plain,
% 39.55/5.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 39.55/5.48      | r1_tarski(X0,X1) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_178394,plain,
% 39.55/5.48      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 39.55/5.48      | r1_tarski(sK0,sK1) = iProver_top ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_11677,c_637]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_2,plain,
% 39.55/5.48      ( r1_tarski(X0,X0) ),
% 39.55/5.48      inference(cnf_transformation,[],[f46]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_639,plain,
% 39.55/5.48      ( r1_tarski(X0,X0) = iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_3,plain,
% 39.55/5.48      ( ~ r1_tarski(X0,X1)
% 39.55/5.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.55/5.48      inference(cnf_transformation,[],[f43]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_638,plain,
% 39.55/5.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.55/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1306,plain,
% 39.55/5.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_639,c_638]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1131,plain,
% 39.55/5.48      ( k3_xboole_0(X0,X0) = X0 ),
% 39.55/5.48      inference(superposition,[status(thm)],[c_639,c_634]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_1945,plain,
% 39.55/5.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.55/5.48      inference(light_normalisation,[status(thm)],[c_1306,c_1131]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_178616,plain,
% 39.55/5.48      ( k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) = iProver_top ),
% 39.55/5.48      inference(demodulation,[status(thm)],[c_178394,c_1945]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_178617,plain,
% 39.55/5.48      ( r1_tarski(sK0,sK1) = iProver_top ),
% 39.55/5.48      inference(equality_resolution_simp,[status(thm)],[c_178616]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_11,negated_conjecture,
% 39.55/5.48      ( ~ r1_tarski(sK0,sK1) ),
% 39.55/5.48      inference(cnf_transformation,[],[f42]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(c_20,plain,
% 39.55/5.48      ( r1_tarski(sK0,sK1) != iProver_top ),
% 39.55/5.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.55/5.48  
% 39.55/5.48  cnf(contradiction,plain,
% 39.55/5.48      ( $false ),
% 39.55/5.48      inference(minisat,[status(thm)],[c_178617,c_20]) ).
% 39.55/5.48  
% 39.55/5.48  
% 39.55/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.55/5.48  
% 39.55/5.48  ------                               Statistics
% 39.55/5.48  
% 39.55/5.48  ------ Selected
% 39.55/5.48  
% 39.55/5.48  total_time:                             4.856
% 39.55/5.48  
%------------------------------------------------------------------------------
