%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:20 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :  127 (2312 expanded)
%              Number of clauses        :   76 (1098 expanded)
%              Number of leaves         :   16 ( 499 expanded)
%              Depth                    :   23
%              Number of atoms          :  225 (3980 expanded)
%              Number of equality atoms :  126 (2055 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).

fof(f69,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f49,f46,f46])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f67,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_611,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
    | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_237,c_14])).

cnf(c_609,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_10,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_683,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_609,c_10])).

cnf(c_19,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_336,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_337,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_647,plain,
    ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_19,c_337])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_357,plain,
    ( k6_relat_1(X0) != X1
    | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_358,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_650,plain,
    ( k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_647,c_358])).

cnf(c_652,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_650,c_10])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_253,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_254,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_258,plain,
    ( k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_14])).

cnf(c_259,plain,
    ( k3_xboole_0(X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_673,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k1_relat_1(k6_relat_1(X1)))) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_259,c_652])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_674,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_673,c_11])).

cnf(c_684,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_683,c_652,c_674])).

cnf(c_8343,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_611,c_684])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_614,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8341,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_614,c_684])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_330,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_14])).

cnf(c_331,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_664,plain,
    ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(light_normalisation,[status(thm)],[c_331,c_647])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_342,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_343,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_639,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_343,c_10,c_11])).

cnf(c_5595,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_664,c_639])).

cnf(c_13077,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X0)) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_8341,c_5595])).

cnf(c_13162,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_13077,c_639,c_8341])).

cnf(c_13503,plain,
    ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(k3_xboole_0(X0,X0)),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_13162,c_664])).

cnf(c_13641,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_13503,c_664])).

cnf(c_13642,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X0))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_13641,c_674])).

cnf(c_22070,plain,
    ( k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_8343,c_13642])).

cnf(c_23055,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_22070,c_674])).

cnf(c_23059,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_23055,c_8343])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1802,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_3196,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1802,c_0])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_612,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8342,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_612,c_684])).

cnf(c_51697,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_8342,c_5595])).

cnf(c_51743,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_51697,c_8342])).

cnf(c_51745,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_51743,c_639])).

cnf(c_55250,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3196,c_51745])).

cnf(c_55424,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_55250,c_3196])).

cnf(c_55666,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))) ),
    inference(superposition,[status(thm)],[c_23059,c_55424])).

cnf(c_2996,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_639,c_674])).

cnf(c_5589,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2996,c_664])).

cnf(c_5626,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_5589,c_664])).

cnf(c_5628,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5626,c_674])).

cnf(c_44991,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_22070,c_5628])).

cnf(c_45084,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_44991,c_8343])).

cnf(c_55770,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_55666,c_23059,c_45084])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_363,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_364,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_20,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_656,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_364,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55770,c_656])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:00:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.86/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.86/3.00  
% 19.86/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.86/3.00  
% 19.86/3.00  ------  iProver source info
% 19.86/3.00  
% 19.86/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.86/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.86/3.00  git: non_committed_changes: false
% 19.86/3.00  git: last_make_outside_of_git: false
% 19.86/3.00  
% 19.86/3.00  ------ 
% 19.86/3.00  
% 19.86/3.00  ------ Input Options
% 19.86/3.00  
% 19.86/3.00  --out_options                           all
% 19.86/3.00  --tptp_safe_out                         true
% 19.86/3.00  --problem_path                          ""
% 19.86/3.00  --include_path                          ""
% 19.86/3.00  --clausifier                            res/vclausify_rel
% 19.86/3.00  --clausifier_options                    --mode clausify
% 19.86/3.00  --stdin                                 false
% 19.86/3.00  --stats_out                             all
% 19.86/3.00  
% 19.86/3.00  ------ General Options
% 19.86/3.00  
% 19.86/3.00  --fof                                   false
% 19.86/3.00  --time_out_real                         305.
% 19.86/3.00  --time_out_virtual                      -1.
% 19.86/3.00  --symbol_type_check                     false
% 19.86/3.00  --clausify_out                          false
% 19.86/3.00  --sig_cnt_out                           false
% 19.86/3.00  --trig_cnt_out                          false
% 19.86/3.00  --trig_cnt_out_tolerance                1.
% 19.86/3.00  --trig_cnt_out_sk_spl                   false
% 19.86/3.00  --abstr_cl_out                          false
% 19.86/3.00  
% 19.86/3.00  ------ Global Options
% 19.86/3.00  
% 19.86/3.00  --schedule                              default
% 19.86/3.00  --add_important_lit                     false
% 19.86/3.00  --prop_solver_per_cl                    1000
% 19.86/3.00  --min_unsat_core                        false
% 19.86/3.00  --soft_assumptions                      false
% 19.86/3.00  --soft_lemma_size                       3
% 19.86/3.00  --prop_impl_unit_size                   0
% 19.86/3.00  --prop_impl_unit                        []
% 19.86/3.00  --share_sel_clauses                     true
% 19.86/3.00  --reset_solvers                         false
% 19.86/3.00  --bc_imp_inh                            [conj_cone]
% 19.86/3.00  --conj_cone_tolerance                   3.
% 19.86/3.00  --extra_neg_conj                        none
% 19.86/3.00  --large_theory_mode                     true
% 19.86/3.00  --prolific_symb_bound                   200
% 19.86/3.00  --lt_threshold                          2000
% 19.86/3.00  --clause_weak_htbl                      true
% 19.86/3.00  --gc_record_bc_elim                     false
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing Options
% 19.86/3.00  
% 19.86/3.00  --preprocessing_flag                    true
% 19.86/3.00  --time_out_prep_mult                    0.1
% 19.86/3.00  --splitting_mode                        input
% 19.86/3.00  --splitting_grd                         true
% 19.86/3.00  --splitting_cvd                         false
% 19.86/3.00  --splitting_cvd_svl                     false
% 19.86/3.00  --splitting_nvd                         32
% 19.86/3.00  --sub_typing                            true
% 19.86/3.00  --prep_gs_sim                           true
% 19.86/3.00  --prep_unflatten                        true
% 19.86/3.00  --prep_res_sim                          true
% 19.86/3.00  --prep_upred                            true
% 19.86/3.00  --prep_sem_filter                       exhaustive
% 19.86/3.00  --prep_sem_filter_out                   false
% 19.86/3.00  --pred_elim                             true
% 19.86/3.00  --res_sim_input                         true
% 19.86/3.00  --eq_ax_congr_red                       true
% 19.86/3.00  --pure_diseq_elim                       true
% 19.86/3.00  --brand_transform                       false
% 19.86/3.00  --non_eq_to_eq                          false
% 19.86/3.00  --prep_def_merge                        true
% 19.86/3.00  --prep_def_merge_prop_impl              false
% 19.86/3.00  --prep_def_merge_mbd                    true
% 19.86/3.00  --prep_def_merge_tr_red                 false
% 19.86/3.00  --prep_def_merge_tr_cl                  false
% 19.86/3.00  --smt_preprocessing                     true
% 19.86/3.00  --smt_ac_axioms                         fast
% 19.86/3.00  --preprocessed_out                      false
% 19.86/3.00  --preprocessed_stats                    false
% 19.86/3.00  
% 19.86/3.00  ------ Abstraction refinement Options
% 19.86/3.00  
% 19.86/3.00  --abstr_ref                             []
% 19.86/3.00  --abstr_ref_prep                        false
% 19.86/3.00  --abstr_ref_until_sat                   false
% 19.86/3.00  --abstr_ref_sig_restrict                funpre
% 19.86/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/3.00  --abstr_ref_under                       []
% 19.86/3.00  
% 19.86/3.00  ------ SAT Options
% 19.86/3.00  
% 19.86/3.00  --sat_mode                              false
% 19.86/3.00  --sat_fm_restart_options                ""
% 19.86/3.00  --sat_gr_def                            false
% 19.86/3.00  --sat_epr_types                         true
% 19.86/3.00  --sat_non_cyclic_types                  false
% 19.86/3.00  --sat_finite_models                     false
% 19.86/3.00  --sat_fm_lemmas                         false
% 19.86/3.00  --sat_fm_prep                           false
% 19.86/3.00  --sat_fm_uc_incr                        true
% 19.86/3.00  --sat_out_model                         small
% 19.86/3.00  --sat_out_clauses                       false
% 19.86/3.00  
% 19.86/3.00  ------ QBF Options
% 19.86/3.00  
% 19.86/3.00  --qbf_mode                              false
% 19.86/3.00  --qbf_elim_univ                         false
% 19.86/3.00  --qbf_dom_inst                          none
% 19.86/3.00  --qbf_dom_pre_inst                      false
% 19.86/3.00  --qbf_sk_in                             false
% 19.86/3.00  --qbf_pred_elim                         true
% 19.86/3.00  --qbf_split                             512
% 19.86/3.00  
% 19.86/3.00  ------ BMC1 Options
% 19.86/3.00  
% 19.86/3.00  --bmc1_incremental                      false
% 19.86/3.00  --bmc1_axioms                           reachable_all
% 19.86/3.00  --bmc1_min_bound                        0
% 19.86/3.00  --bmc1_max_bound                        -1
% 19.86/3.00  --bmc1_max_bound_default                -1
% 19.86/3.00  --bmc1_symbol_reachability              true
% 19.86/3.00  --bmc1_property_lemmas                  false
% 19.86/3.00  --bmc1_k_induction                      false
% 19.86/3.00  --bmc1_non_equiv_states                 false
% 19.86/3.00  --bmc1_deadlock                         false
% 19.86/3.00  --bmc1_ucm                              false
% 19.86/3.00  --bmc1_add_unsat_core                   none
% 19.86/3.00  --bmc1_unsat_core_children              false
% 19.86/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/3.00  --bmc1_out_stat                         full
% 19.86/3.00  --bmc1_ground_init                      false
% 19.86/3.00  --bmc1_pre_inst_next_state              false
% 19.86/3.00  --bmc1_pre_inst_state                   false
% 19.86/3.00  --bmc1_pre_inst_reach_state             false
% 19.86/3.00  --bmc1_out_unsat_core                   false
% 19.86/3.00  --bmc1_aig_witness_out                  false
% 19.86/3.00  --bmc1_verbose                          false
% 19.86/3.00  --bmc1_dump_clauses_tptp                false
% 19.86/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.86/3.00  --bmc1_dump_file                        -
% 19.86/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.86/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.86/3.00  --bmc1_ucm_extend_mode                  1
% 19.86/3.00  --bmc1_ucm_init_mode                    2
% 19.86/3.00  --bmc1_ucm_cone_mode                    none
% 19.86/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.86/3.00  --bmc1_ucm_relax_model                  4
% 19.86/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.86/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/3.00  --bmc1_ucm_layered_model                none
% 19.86/3.00  --bmc1_ucm_max_lemma_size               10
% 19.86/3.00  
% 19.86/3.00  ------ AIG Options
% 19.86/3.00  
% 19.86/3.00  --aig_mode                              false
% 19.86/3.00  
% 19.86/3.00  ------ Instantiation Options
% 19.86/3.00  
% 19.86/3.00  --instantiation_flag                    true
% 19.86/3.00  --inst_sos_flag                         false
% 19.86/3.00  --inst_sos_phase                        true
% 19.86/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel_side                     num_symb
% 19.86/3.00  --inst_solver_per_active                1400
% 19.86/3.00  --inst_solver_calls_frac                1.
% 19.86/3.00  --inst_passive_queue_type               priority_queues
% 19.86/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/3.00  --inst_passive_queues_freq              [25;2]
% 19.86/3.00  --inst_dismatching                      true
% 19.86/3.00  --inst_eager_unprocessed_to_passive     true
% 19.86/3.00  --inst_prop_sim_given                   true
% 19.86/3.00  --inst_prop_sim_new                     false
% 19.86/3.00  --inst_subs_new                         false
% 19.86/3.00  --inst_eq_res_simp                      false
% 19.86/3.00  --inst_subs_given                       false
% 19.86/3.00  --inst_orphan_elimination               true
% 19.86/3.00  --inst_learning_loop_flag               true
% 19.86/3.00  --inst_learning_start                   3000
% 19.86/3.00  --inst_learning_factor                  2
% 19.86/3.00  --inst_start_prop_sim_after_learn       3
% 19.86/3.00  --inst_sel_renew                        solver
% 19.86/3.00  --inst_lit_activity_flag                true
% 19.86/3.00  --inst_restr_to_given                   false
% 19.86/3.00  --inst_activity_threshold               500
% 19.86/3.00  --inst_out_proof                        true
% 19.86/3.00  
% 19.86/3.00  ------ Resolution Options
% 19.86/3.00  
% 19.86/3.00  --resolution_flag                       true
% 19.86/3.00  --res_lit_sel                           adaptive
% 19.86/3.00  --res_lit_sel_side                      none
% 19.86/3.00  --res_ordering                          kbo
% 19.86/3.00  --res_to_prop_solver                    active
% 19.86/3.00  --res_prop_simpl_new                    false
% 19.86/3.00  --res_prop_simpl_given                  true
% 19.86/3.00  --res_passive_queue_type                priority_queues
% 19.86/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/3.00  --res_passive_queues_freq               [15;5]
% 19.86/3.00  --res_forward_subs                      full
% 19.86/3.00  --res_backward_subs                     full
% 19.86/3.00  --res_forward_subs_resolution           true
% 19.86/3.00  --res_backward_subs_resolution          true
% 19.86/3.00  --res_orphan_elimination                true
% 19.86/3.00  --res_time_limit                        2.
% 19.86/3.00  --res_out_proof                         true
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Options
% 19.86/3.00  
% 19.86/3.00  --superposition_flag                    true
% 19.86/3.00  --sup_passive_queue_type                priority_queues
% 19.86/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.86/3.00  --demod_completeness_check              fast
% 19.86/3.00  --demod_use_ground                      true
% 19.86/3.00  --sup_to_prop_solver                    passive
% 19.86/3.00  --sup_prop_simpl_new                    true
% 19.86/3.00  --sup_prop_simpl_given                  true
% 19.86/3.00  --sup_fun_splitting                     false
% 19.86/3.00  --sup_smt_interval                      50000
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Simplification Setup
% 19.86/3.00  
% 19.86/3.00  --sup_indices_passive                   []
% 19.86/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.00  --sup_full_bw                           [BwDemod]
% 19.86/3.00  --sup_immed_triv                        [TrivRules]
% 19.86/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.00  --sup_immed_bw_main                     []
% 19.86/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/3.00  
% 19.86/3.00  ------ Combination Options
% 19.86/3.00  
% 19.86/3.00  --comb_res_mult                         3
% 19.86/3.00  --comb_sup_mult                         2
% 19.86/3.00  --comb_inst_mult                        10
% 19.86/3.00  
% 19.86/3.00  ------ Debug Options
% 19.86/3.00  
% 19.86/3.00  --dbg_backtrace                         false
% 19.86/3.00  --dbg_dump_prop_clauses                 false
% 19.86/3.00  --dbg_dump_prop_clauses_file            -
% 19.86/3.00  --dbg_out_stat                          false
% 19.86/3.00  ------ Parsing...
% 19.86/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.86/3.00  ------ Proving...
% 19.86/3.00  ------ Problem Properties 
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  clauses                                 27
% 19.86/3.00  conjectures                             2
% 19.86/3.00  EPR                                     3
% 19.86/3.00  Horn                                    27
% 19.86/3.00  unary                                   21
% 19.86/3.00  binary                                  2
% 19.86/3.00  lits                                    37
% 19.86/3.00  lits eq                                 19
% 19.86/3.00  fd_pure                                 0
% 19.86/3.00  fd_pseudo                               0
% 19.86/3.00  fd_cond                                 0
% 19.86/3.00  fd_pseudo_cond                          1
% 19.86/3.00  AC symbols                              0
% 19.86/3.00  
% 19.86/3.00  ------ Schedule dynamic 5 is on 
% 19.86/3.00  
% 19.86/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  ------ 
% 19.86/3.00  Current options:
% 19.86/3.00  ------ 
% 19.86/3.00  
% 19.86/3.00  ------ Input Options
% 19.86/3.00  
% 19.86/3.00  --out_options                           all
% 19.86/3.00  --tptp_safe_out                         true
% 19.86/3.00  --problem_path                          ""
% 19.86/3.00  --include_path                          ""
% 19.86/3.00  --clausifier                            res/vclausify_rel
% 19.86/3.00  --clausifier_options                    --mode clausify
% 19.86/3.00  --stdin                                 false
% 19.86/3.00  --stats_out                             all
% 19.86/3.00  
% 19.86/3.00  ------ General Options
% 19.86/3.00  
% 19.86/3.00  --fof                                   false
% 19.86/3.00  --time_out_real                         305.
% 19.86/3.00  --time_out_virtual                      -1.
% 19.86/3.00  --symbol_type_check                     false
% 19.86/3.00  --clausify_out                          false
% 19.86/3.00  --sig_cnt_out                           false
% 19.86/3.00  --trig_cnt_out                          false
% 19.86/3.00  --trig_cnt_out_tolerance                1.
% 19.86/3.00  --trig_cnt_out_sk_spl                   false
% 19.86/3.00  --abstr_cl_out                          false
% 19.86/3.00  
% 19.86/3.00  ------ Global Options
% 19.86/3.00  
% 19.86/3.00  --schedule                              default
% 19.86/3.00  --add_important_lit                     false
% 19.86/3.00  --prop_solver_per_cl                    1000
% 19.86/3.00  --min_unsat_core                        false
% 19.86/3.00  --soft_assumptions                      false
% 19.86/3.00  --soft_lemma_size                       3
% 19.86/3.00  --prop_impl_unit_size                   0
% 19.86/3.00  --prop_impl_unit                        []
% 19.86/3.00  --share_sel_clauses                     true
% 19.86/3.00  --reset_solvers                         false
% 19.86/3.00  --bc_imp_inh                            [conj_cone]
% 19.86/3.00  --conj_cone_tolerance                   3.
% 19.86/3.00  --extra_neg_conj                        none
% 19.86/3.00  --large_theory_mode                     true
% 19.86/3.00  --prolific_symb_bound                   200
% 19.86/3.00  --lt_threshold                          2000
% 19.86/3.00  --clause_weak_htbl                      true
% 19.86/3.00  --gc_record_bc_elim                     false
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing Options
% 19.86/3.00  
% 19.86/3.00  --preprocessing_flag                    true
% 19.86/3.00  --time_out_prep_mult                    0.1
% 19.86/3.00  --splitting_mode                        input
% 19.86/3.00  --splitting_grd                         true
% 19.86/3.00  --splitting_cvd                         false
% 19.86/3.00  --splitting_cvd_svl                     false
% 19.86/3.00  --splitting_nvd                         32
% 19.86/3.00  --sub_typing                            true
% 19.86/3.00  --prep_gs_sim                           true
% 19.86/3.00  --prep_unflatten                        true
% 19.86/3.00  --prep_res_sim                          true
% 19.86/3.00  --prep_upred                            true
% 19.86/3.00  --prep_sem_filter                       exhaustive
% 19.86/3.00  --prep_sem_filter_out                   false
% 19.86/3.00  --pred_elim                             true
% 19.86/3.00  --res_sim_input                         true
% 19.86/3.01  --eq_ax_congr_red                       true
% 19.86/3.01  --pure_diseq_elim                       true
% 19.86/3.01  --brand_transform                       false
% 19.86/3.01  --non_eq_to_eq                          false
% 19.86/3.01  --prep_def_merge                        true
% 19.86/3.01  --prep_def_merge_prop_impl              false
% 19.86/3.01  --prep_def_merge_mbd                    true
% 19.86/3.01  --prep_def_merge_tr_red                 false
% 19.86/3.01  --prep_def_merge_tr_cl                  false
% 19.86/3.01  --smt_preprocessing                     true
% 19.86/3.01  --smt_ac_axioms                         fast
% 19.86/3.01  --preprocessed_out                      false
% 19.86/3.01  --preprocessed_stats                    false
% 19.86/3.01  
% 19.86/3.01  ------ Abstraction refinement Options
% 19.86/3.01  
% 19.86/3.01  --abstr_ref                             []
% 19.86/3.01  --abstr_ref_prep                        false
% 19.86/3.01  --abstr_ref_until_sat                   false
% 19.86/3.01  --abstr_ref_sig_restrict                funpre
% 19.86/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/3.01  --abstr_ref_under                       []
% 19.86/3.01  
% 19.86/3.01  ------ SAT Options
% 19.86/3.01  
% 19.86/3.01  --sat_mode                              false
% 19.86/3.01  --sat_fm_restart_options                ""
% 19.86/3.01  --sat_gr_def                            false
% 19.86/3.01  --sat_epr_types                         true
% 19.86/3.01  --sat_non_cyclic_types                  false
% 19.86/3.01  --sat_finite_models                     false
% 19.86/3.01  --sat_fm_lemmas                         false
% 19.86/3.01  --sat_fm_prep                           false
% 19.86/3.01  --sat_fm_uc_incr                        true
% 19.86/3.01  --sat_out_model                         small
% 19.86/3.01  --sat_out_clauses                       false
% 19.86/3.01  
% 19.86/3.01  ------ QBF Options
% 19.86/3.01  
% 19.86/3.01  --qbf_mode                              false
% 19.86/3.01  --qbf_elim_univ                         false
% 19.86/3.01  --qbf_dom_inst                          none
% 19.86/3.01  --qbf_dom_pre_inst                      false
% 19.86/3.01  --qbf_sk_in                             false
% 19.86/3.01  --qbf_pred_elim                         true
% 19.86/3.01  --qbf_split                             512
% 19.86/3.01  
% 19.86/3.01  ------ BMC1 Options
% 19.86/3.01  
% 19.86/3.01  --bmc1_incremental                      false
% 19.86/3.01  --bmc1_axioms                           reachable_all
% 19.86/3.01  --bmc1_min_bound                        0
% 19.86/3.01  --bmc1_max_bound                        -1
% 19.86/3.01  --bmc1_max_bound_default                -1
% 19.86/3.01  --bmc1_symbol_reachability              true
% 19.86/3.01  --bmc1_property_lemmas                  false
% 19.86/3.01  --bmc1_k_induction                      false
% 19.86/3.01  --bmc1_non_equiv_states                 false
% 19.86/3.01  --bmc1_deadlock                         false
% 19.86/3.01  --bmc1_ucm                              false
% 19.86/3.01  --bmc1_add_unsat_core                   none
% 19.86/3.01  --bmc1_unsat_core_children              false
% 19.86/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/3.01  --bmc1_out_stat                         full
% 19.86/3.01  --bmc1_ground_init                      false
% 19.86/3.01  --bmc1_pre_inst_next_state              false
% 19.86/3.01  --bmc1_pre_inst_state                   false
% 19.86/3.01  --bmc1_pre_inst_reach_state             false
% 19.86/3.01  --bmc1_out_unsat_core                   false
% 19.86/3.01  --bmc1_aig_witness_out                  false
% 19.86/3.01  --bmc1_verbose                          false
% 19.86/3.01  --bmc1_dump_clauses_tptp                false
% 19.86/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.86/3.01  --bmc1_dump_file                        -
% 19.86/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.86/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.86/3.01  --bmc1_ucm_extend_mode                  1
% 19.86/3.01  --bmc1_ucm_init_mode                    2
% 19.86/3.01  --bmc1_ucm_cone_mode                    none
% 19.86/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.86/3.01  --bmc1_ucm_relax_model                  4
% 19.86/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.86/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/3.01  --bmc1_ucm_layered_model                none
% 19.86/3.01  --bmc1_ucm_max_lemma_size               10
% 19.86/3.01  
% 19.86/3.01  ------ AIG Options
% 19.86/3.01  
% 19.86/3.01  --aig_mode                              false
% 19.86/3.01  
% 19.86/3.01  ------ Instantiation Options
% 19.86/3.01  
% 19.86/3.01  --instantiation_flag                    true
% 19.86/3.01  --inst_sos_flag                         false
% 19.86/3.01  --inst_sos_phase                        true
% 19.86/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/3.01  --inst_lit_sel_side                     none
% 19.86/3.01  --inst_solver_per_active                1400
% 19.86/3.01  --inst_solver_calls_frac                1.
% 19.86/3.01  --inst_passive_queue_type               priority_queues
% 19.86/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/3.01  --inst_passive_queues_freq              [25;2]
% 19.86/3.01  --inst_dismatching                      true
% 19.86/3.01  --inst_eager_unprocessed_to_passive     true
% 19.86/3.01  --inst_prop_sim_given                   true
% 19.86/3.01  --inst_prop_sim_new                     false
% 19.86/3.01  --inst_subs_new                         false
% 19.86/3.01  --inst_eq_res_simp                      false
% 19.86/3.01  --inst_subs_given                       false
% 19.86/3.01  --inst_orphan_elimination               true
% 19.86/3.01  --inst_learning_loop_flag               true
% 19.86/3.01  --inst_learning_start                   3000
% 19.86/3.01  --inst_learning_factor                  2
% 19.86/3.01  --inst_start_prop_sim_after_learn       3
% 19.86/3.01  --inst_sel_renew                        solver
% 19.86/3.01  --inst_lit_activity_flag                true
% 19.86/3.01  --inst_restr_to_given                   false
% 19.86/3.01  --inst_activity_threshold               500
% 19.86/3.01  --inst_out_proof                        true
% 19.86/3.01  
% 19.86/3.01  ------ Resolution Options
% 19.86/3.01  
% 19.86/3.01  --resolution_flag                       false
% 19.86/3.01  --res_lit_sel                           adaptive
% 19.86/3.01  --res_lit_sel_side                      none
% 19.86/3.01  --res_ordering                          kbo
% 19.86/3.01  --res_to_prop_solver                    active
% 19.86/3.01  --res_prop_simpl_new                    false
% 19.86/3.01  --res_prop_simpl_given                  true
% 19.86/3.01  --res_passive_queue_type                priority_queues
% 19.86/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/3.01  --res_passive_queues_freq               [15;5]
% 19.86/3.01  --res_forward_subs                      full
% 19.86/3.01  --res_backward_subs                     full
% 19.86/3.01  --res_forward_subs_resolution           true
% 19.86/3.01  --res_backward_subs_resolution          true
% 19.86/3.01  --res_orphan_elimination                true
% 19.86/3.01  --res_time_limit                        2.
% 19.86/3.01  --res_out_proof                         true
% 19.86/3.01  
% 19.86/3.01  ------ Superposition Options
% 19.86/3.01  
% 19.86/3.01  --superposition_flag                    true
% 19.86/3.01  --sup_passive_queue_type                priority_queues
% 19.86/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.86/3.01  --demod_completeness_check              fast
% 19.86/3.01  --demod_use_ground                      true
% 19.86/3.01  --sup_to_prop_solver                    passive
% 19.86/3.01  --sup_prop_simpl_new                    true
% 19.86/3.01  --sup_prop_simpl_given                  true
% 19.86/3.01  --sup_fun_splitting                     false
% 19.86/3.01  --sup_smt_interval                      50000
% 19.86/3.01  
% 19.86/3.01  ------ Superposition Simplification Setup
% 19.86/3.01  
% 19.86/3.01  --sup_indices_passive                   []
% 19.86/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.01  --sup_full_bw                           [BwDemod]
% 19.86/3.01  --sup_immed_triv                        [TrivRules]
% 19.86/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.01  --sup_immed_bw_main                     []
% 19.86/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.86/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.86/3.01  
% 19.86/3.01  ------ Combination Options
% 19.86/3.01  
% 19.86/3.01  --comb_res_mult                         3
% 19.86/3.01  --comb_sup_mult                         2
% 19.86/3.01  --comb_inst_mult                        10
% 19.86/3.01  
% 19.86/3.01  ------ Debug Options
% 19.86/3.01  
% 19.86/3.01  --dbg_backtrace                         false
% 19.86/3.01  --dbg_dump_prop_clauses                 false
% 19.86/3.01  --dbg_dump_prop_clauses_file            -
% 19.86/3.01  --dbg_out_stat                          false
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  ------ Proving...
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  % SZS status Theorem for theBenchmark.p
% 19.86/3.01  
% 19.86/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.86/3.01  
% 19.86/3.01  fof(f21,conjecture,(
% 19.86/3.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f22,negated_conjecture,(
% 19.86/3.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 19.86/3.01    inference(negated_conjecture,[],[f21])).
% 19.86/3.01  
% 19.86/3.01  fof(f36,plain,(
% 19.86/3.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 19.86/3.01    inference(ennf_transformation,[],[f22])).
% 19.86/3.01  
% 19.86/3.01  fof(f37,plain,(
% 19.86/3.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 19.86/3.01    inference(flattening,[],[f36])).
% 19.86/3.01  
% 19.86/3.01  fof(f41,plain,(
% 19.86/3.01    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 19.86/3.01    introduced(choice_axiom,[])).
% 19.86/3.01  
% 19.86/3.01  fof(f40,plain,(
% 19.86/3.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 19.86/3.01    introduced(choice_axiom,[])).
% 19.86/3.01  
% 19.86/3.01  fof(f42,plain,(
% 19.86/3.01    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 19.86/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).
% 19.86/3.01  
% 19.86/3.01  fof(f69,plain,(
% 19.86/3.01    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 19.86/3.01    inference(cnf_transformation,[],[f42])).
% 19.86/3.01  
% 19.86/3.01  fof(f15,axiom,(
% 19.86/3.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f61,plain,(
% 19.86/3.01    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 19.86/3.01    inference(cnf_transformation,[],[f15])).
% 19.86/3.01  
% 19.86/3.01  fof(f17,axiom,(
% 19.86/3.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f30,plain,(
% 19.86/3.01    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.86/3.01    inference(ennf_transformation,[],[f17])).
% 19.86/3.01  
% 19.86/3.01  fof(f31,plain,(
% 19.86/3.01    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.86/3.01    inference(flattening,[],[f30])).
% 19.86/3.01  
% 19.86/3.01  fof(f63,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f31])).
% 19.86/3.01  
% 19.86/3.01  fof(f60,plain,(
% 19.86/3.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.86/3.01    inference(cnf_transformation,[],[f15])).
% 19.86/3.01  
% 19.86/3.01  fof(f13,axiom,(
% 19.86/3.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f58,plain,(
% 19.86/3.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.86/3.01    inference(cnf_transformation,[],[f13])).
% 19.86/3.01  
% 19.86/3.01  fof(f20,axiom,(
% 19.86/3.01    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f66,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 19.86/3.01    inference(cnf_transformation,[],[f20])).
% 19.86/3.01  
% 19.86/3.01  fof(f14,axiom,(
% 19.86/3.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f28,plain,(
% 19.86/3.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 19.86/3.01    inference(ennf_transformation,[],[f14])).
% 19.86/3.01  
% 19.86/3.01  fof(f59,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f28])).
% 19.86/3.01  
% 19.86/3.01  fof(f10,axiom,(
% 19.86/3.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f25,plain,(
% 19.86/3.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.86/3.01    inference(ennf_transformation,[],[f10])).
% 19.86/3.01  
% 19.86/3.01  fof(f54,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f25])).
% 19.86/3.01  
% 19.86/3.01  fof(f18,axiom,(
% 19.86/3.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f32,plain,(
% 19.86/3.01    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.86/3.01    inference(ennf_transformation,[],[f18])).
% 19.86/3.01  
% 19.86/3.01  fof(f33,plain,(
% 19.86/3.01    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.86/3.01    inference(flattening,[],[f32])).
% 19.86/3.01  
% 19.86/3.01  fof(f64,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f33])).
% 19.86/3.01  
% 19.86/3.01  fof(f57,plain,(
% 19.86/3.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.86/3.01    inference(cnf_transformation,[],[f13])).
% 19.86/3.01  
% 19.86/3.01  fof(f1,axiom,(
% 19.86/3.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f38,plain,(
% 19.86/3.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.86/3.01    inference(nnf_transformation,[],[f1])).
% 19.86/3.01  
% 19.86/3.01  fof(f39,plain,(
% 19.86/3.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.86/3.01    inference(flattening,[],[f38])).
% 19.86/3.01  
% 19.86/3.01  fof(f43,plain,(
% 19.86/3.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.86/3.01    inference(cnf_transformation,[],[f39])).
% 19.86/3.01  
% 19.86/3.01  fof(f77,plain,(
% 19.86/3.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.86/3.01    inference(equality_resolution,[],[f43])).
% 19.86/3.01  
% 19.86/3.01  fof(f16,axiom,(
% 19.86/3.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f29,plain,(
% 19.86/3.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.86/3.01    inference(ennf_transformation,[],[f16])).
% 19.86/3.01  
% 19.86/3.01  fof(f62,plain,(
% 19.86/3.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f29])).
% 19.86/3.01  
% 19.86/3.01  fof(f12,axiom,(
% 19.86/3.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f27,plain,(
% 19.86/3.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 19.86/3.01    inference(ennf_transformation,[],[f12])).
% 19.86/3.01  
% 19.86/3.01  fof(f56,plain,(
% 19.86/3.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f27])).
% 19.86/3.01  
% 19.86/3.01  fof(f5,axiom,(
% 19.86/3.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f49,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f5])).
% 19.86/3.01  
% 19.86/3.01  fof(f2,axiom,(
% 19.86/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f46,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.86/3.01    inference(cnf_transformation,[],[f2])).
% 19.86/3.01  
% 19.86/3.01  fof(f73,plain,(
% 19.86/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 19.86/3.01    inference(definition_unfolding,[],[f49,f46,f46])).
% 19.86/3.01  
% 19.86/3.01  fof(f4,axiom,(
% 19.86/3.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.86/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.01  
% 19.86/3.01  fof(f48,plain,(
% 19.86/3.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.86/3.01    inference(cnf_transformation,[],[f4])).
% 19.86/3.01  
% 19.86/3.01  fof(f74,plain,(
% 19.86/3.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 19.86/3.01    inference(definition_unfolding,[],[f48,f46])).
% 19.86/3.01  
% 19.86/3.01  fof(f67,plain,(
% 19.86/3.01    v1_relat_1(sK0)),
% 19.86/3.01    inference(cnf_transformation,[],[f42])).
% 19.86/3.01  
% 19.86/3.01  fof(f70,plain,(
% 19.86/3.01    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 19.86/3.01    inference(cnf_transformation,[],[f42])).
% 19.86/3.01  
% 19.86/3.01  cnf(c_21,negated_conjecture,
% 19.86/3.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 19.86/3.01      inference(cnf_transformation,[],[f69]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_611,plain,
% 19.86/3.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 19.86/3.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13,plain,
% 19.86/3.01      ( v1_funct_1(k6_relat_1(X0)) ),
% 19.86/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_16,plain,
% 19.86/3.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 19.86/3.01      | ~ v1_funct_1(X1)
% 19.86/3.01      | ~ v1_relat_1(X1)
% 19.86/3.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 19.86/3.01      inference(cnf_transformation,[],[f63]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_236,plain,
% 19.86/3.01      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 19.86/3.01      | ~ v1_relat_1(X1)
% 19.86/3.01      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 19.86/3.01      | k6_relat_1(X2) != X1 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_237,plain,
% 19.86/3.01      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 19.86/3.01      | ~ v1_relat_1(k6_relat_1(X1))
% 19.86/3.01      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_236]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_14,plain,
% 19.86/3.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.86/3.01      inference(cnf_transformation,[],[f60]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_247,plain,
% 19.86/3.01      ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
% 19.86/3.01      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ),
% 19.86/3.01      inference(forward_subsumption_resolution,
% 19.86/3.01                [status(thm)],
% 19.86/3.01                [c_237,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_609,plain,
% 19.86/3.01      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 19.86/3.01      | r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) != iProver_top ),
% 19.86/3.01      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_10,plain,
% 19.86/3.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.86/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_683,plain,
% 19.86/3.01      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1
% 19.86/3.01      | r1_tarski(X1,X0) != iProver_top ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_609,c_10]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_19,plain,
% 19.86/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
% 19.86/3.01      inference(cnf_transformation,[],[f66]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_12,plain,
% 19.86/3.01      ( ~ v1_relat_1(X0)
% 19.86/3.01      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.86/3.01      inference(cnf_transformation,[],[f59]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_336,plain,
% 19.86/3.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 19.86/3.01      | k6_relat_1(X2) != X1 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_337,plain,
% 19.86/3.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_336]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_647,plain,
% 19.86/3.01      ( k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_19,c_337]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_7,plain,
% 19.86/3.01      ( ~ v1_relat_1(X0)
% 19.86/3.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.86/3.01      inference(cnf_transformation,[],[f54]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_357,plain,
% 19.86/3.01      ( k6_relat_1(X0) != X1
% 19.86/3.01      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_358,plain,
% 19.86/3.01      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_357]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_650,plain,
% 19.86/3.01      ( k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_647,c_358]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_652,plain,
% 19.86/3.01      ( k9_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,X1) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_650,c_10]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_17,plain,
% 19.86/3.01      ( ~ v1_funct_1(X0)
% 19.86/3.01      | ~ v1_relat_1(X0)
% 19.86/3.01      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 19.86/3.01      inference(cnf_transformation,[],[f64]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_253,plain,
% 19.86/3.01      ( ~ v1_relat_1(X0)
% 19.86/3.01      | k3_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 19.86/3.01      | k6_relat_1(X2) != X0 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_254,plain,
% 19.86/3.01      ( ~ v1_relat_1(k6_relat_1(X0))
% 19.86/3.01      | k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_253]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_258,plain,
% 19.86/3.01      ( k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 19.86/3.01      inference(global_propositional_subsumption,
% 19.86/3.01                [status(thm)],
% 19.86/3.01                [c_254,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_259,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 19.86/3.01      inference(renaming,[status(thm)],[c_258]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_673,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X1,k1_relat_1(k6_relat_1(X1)))) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X1),X0)) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_259,c_652]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_11,plain,
% 19.86/3.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.86/3.01      inference(cnf_transformation,[],[f57]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_674,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_673,c_11]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_684,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X1,X1)) = X0
% 19.86/3.01      | r1_tarski(X0,X1) != iProver_top ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_683,c_652,c_674]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_8343,plain,
% 19.86/3.01      ( k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) = k10_relat_1(sK0,sK2) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_611,c_684]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_3,plain,
% 19.86/3.01      ( r1_tarski(X0,X0) ),
% 19.86/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_614,plain,
% 19.86/3.01      ( r1_tarski(X0,X0) = iProver_top ),
% 19.86/3.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_8341,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_614,c_684]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_15,plain,
% 19.86/3.01      ( ~ v1_relat_1(X0)
% 19.86/3.01      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 19.86/3.01      inference(cnf_transformation,[],[f62]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_330,plain,
% 19.86/3.01      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 19.86/3.01      | k6_relat_1(X3) != X0 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_15,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_331,plain,
% 19.86/3.01      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_330]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_664,plain,
% 19.86/3.01      ( k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) = k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_331,c_647]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_9,plain,
% 19.86/3.01      ( ~ v1_relat_1(X0)
% 19.86/3.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 19.86/3.01      inference(cnf_transformation,[],[f56]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_342,plain,
% 19.86/3.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 19.86/3.01      | k6_relat_1(X1) != X0 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_343,plain,
% 19.86/3.01      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_342]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_639,plain,
% 19.86/3.01      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_343,c_10,c_11]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_5595,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_664,c_639]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13077,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X0)) = k3_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_8341,c_5595]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13162,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),X0) = X0 ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_13077,c_639,c_8341]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13503,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(k3_xboole_0(X0,X0)),X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_13162,c_664]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13641,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_13503,c_664]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_13642,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X0))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_13641,c_674]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_22070,plain,
% 19.86/3.01      ( k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_8343,c_13642]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_23055,plain,
% 19.86/3.01      ( k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_22070,c_674]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_23059,plain,
% 19.86/3.01      ( k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_23055,c_8343]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_0,plain,
% 19.86/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 19.86/3.01      inference(cnf_transformation,[],[f73]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_1802,plain,
% 19.86/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_3196,plain,
% 19.86/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_1802,c_0]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_5,plain,
% 19.86/3.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 19.86/3.01      inference(cnf_transformation,[],[f74]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_612,plain,
% 19.86/3.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.86/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_8342,plain,
% 19.86/3.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_612,c_684]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_51697,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X0)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_8342,c_5595]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_51743,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_51697,c_8342]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_51745,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_51743,c_639]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_55250,plain,
% 19.86/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_3196,c_51745]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_55424,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_55250,c_3196]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_55666,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_23059,c_55424]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_2996,plain,
% 19.86/3.01      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_639,c_674]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_5589,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X0)),X1) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_2996,c_664]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_5626,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_5589,c_664]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_5628,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(X0,X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_5626,c_674]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_44991,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k3_xboole_0(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,sK1)) ),
% 19.86/3.01      inference(superposition,[status(thm)],[c_22070,c_5628]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_45084,plain,
% 19.86/3.01      ( k3_xboole_0(k3_xboole_0(sK1,sK1),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) = k10_relat_1(sK0,sK2) ),
% 19.86/3.01      inference(light_normalisation,[status(thm)],[c_44991,c_8343]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_55770,plain,
% 19.86/3.01      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
% 19.86/3.01      inference(light_normalisation,
% 19.86/3.01                [status(thm)],
% 19.86/3.01                [c_55666,c_23059,c_45084]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_23,negated_conjecture,
% 19.86/3.01      ( v1_relat_1(sK0) ),
% 19.86/3.01      inference(cnf_transformation,[],[f67]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_363,plain,
% 19.86/3.01      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 19.86/3.01      | sK0 != X0 ),
% 19.86/3.01      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_364,plain,
% 19.86/3.01      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
% 19.86/3.01      inference(unflattening,[status(thm)],[c_363]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_20,negated_conjecture,
% 19.86/3.01      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 19.86/3.01      inference(cnf_transformation,[],[f70]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(c_656,plain,
% 19.86/3.01      ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) != k10_relat_1(sK0,sK2) ),
% 19.86/3.01      inference(demodulation,[status(thm)],[c_364,c_20]) ).
% 19.86/3.01  
% 19.86/3.01  cnf(contradiction,plain,
% 19.86/3.01      ( $false ),
% 19.86/3.01      inference(minisat,[status(thm)],[c_55770,c_656]) ).
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.86/3.01  
% 19.86/3.01  ------                               Statistics
% 19.86/3.01  
% 19.86/3.01  ------ General
% 19.86/3.01  
% 19.86/3.01  abstr_ref_over_cycles:                  0
% 19.86/3.01  abstr_ref_under_cycles:                 0
% 19.86/3.01  gc_basic_clause_elim:                   0
% 19.86/3.01  forced_gc_time:                         0
% 19.86/3.01  parsing_time:                           0.01
% 19.86/3.01  unif_index_cands_time:                  0.
% 19.86/3.01  unif_index_add_time:                    0.
% 19.86/3.01  orderings_time:                         0.
% 19.86/3.01  out_proof_time:                         0.01
% 19.86/3.01  total_time:                             2.368
% 19.86/3.01  num_of_symbols:                         48
% 19.86/3.01  num_of_terms:                           58973
% 19.86/3.01  
% 19.86/3.01  ------ Preprocessing
% 19.86/3.01  
% 19.86/3.01  num_of_splits:                          0
% 19.86/3.01  num_of_split_atoms:                     0
% 19.86/3.01  num_of_reused_defs:                     0
% 19.86/3.01  num_eq_ax_congr_red:                    15
% 19.86/3.01  num_of_sem_filtered_clauses:            1
% 19.86/3.01  num_of_subtypes:                        0
% 19.86/3.01  monotx_restored_types:                  0
% 19.86/3.01  sat_num_of_epr_types:                   0
% 19.86/3.01  sat_num_of_non_cyclic_types:            0
% 19.86/3.01  sat_guarded_non_collapsed_types:        0
% 19.86/3.01  num_pure_diseq_elim:                    0
% 19.86/3.01  simp_replaced_by:                       0
% 19.86/3.01  res_preprocessed:                       104
% 19.86/3.01  prep_upred:                             0
% 19.86/3.01  prep_unflattend:                        16
% 19.86/3.01  smt_new_axioms:                         0
% 19.86/3.01  pred_elim_cands:                        3
% 19.86/3.01  pred_elim:                              2
% 19.86/3.01  pred_elim_cl:                           -4
% 19.86/3.01  pred_elim_cycles:                       3
% 19.86/3.01  merged_defs:                            0
% 19.86/3.01  merged_defs_ncl:                        0
% 19.86/3.01  bin_hyper_res:                          0
% 19.86/3.01  prep_cycles:                            3
% 19.86/3.01  pred_elim_time:                         0.006
% 19.86/3.01  splitting_time:                         0.
% 19.86/3.01  sem_filter_time:                        0.
% 19.86/3.01  monotx_time:                            0.001
% 19.86/3.01  subtype_inf_time:                       0.
% 19.86/3.01  
% 19.86/3.01  ------ Problem properties
% 19.86/3.01  
% 19.86/3.01  clauses:                                27
% 19.86/3.01  conjectures:                            2
% 19.86/3.01  epr:                                    3
% 19.86/3.01  horn:                                   27
% 19.86/3.01  ground:                                 3
% 19.86/3.01  unary:                                  21
% 19.86/3.01  binary:                                 2
% 19.86/3.01  lits:                                   37
% 19.86/3.01  lits_eq:                                19
% 19.86/3.01  fd_pure:                                0
% 19.86/3.01  fd_pseudo:                              0
% 19.86/3.01  fd_cond:                                0
% 19.86/3.01  fd_pseudo_cond:                         1
% 19.86/3.01  ac_symbols:                             0
% 19.86/3.01  
% 19.86/3.01  ------ Propositional Solver
% 19.86/3.01  
% 19.86/3.01  prop_solver_calls:                      27
% 19.86/3.01  prop_fast_solver_calls:                 1604
% 19.86/3.01  smt_solver_calls:                       0
% 19.86/3.01  smt_fast_solver_calls:                  0
% 19.86/3.01  prop_num_of_clauses:                    15177
% 19.86/3.01  prop_preprocess_simplified:             22570
% 19.86/3.01  prop_fo_subsumed:                       67
% 19.86/3.01  prop_solver_time:                       0.
% 19.86/3.01  smt_solver_time:                        0.
% 19.86/3.01  smt_fast_solver_time:                   0.
% 19.86/3.01  prop_fast_solver_time:                  0.
% 19.86/3.01  prop_unsat_core_time:                   0.001
% 19.86/3.01  
% 19.86/3.01  ------ QBF
% 19.86/3.01  
% 19.86/3.01  qbf_q_res:                              0
% 19.86/3.01  qbf_num_tautologies:                    0
% 19.86/3.01  qbf_prep_cycles:                        0
% 19.86/3.01  
% 19.86/3.01  ------ BMC1
% 19.86/3.01  
% 19.86/3.01  bmc1_current_bound:                     -1
% 19.86/3.01  bmc1_last_solved_bound:                 -1
% 19.86/3.01  bmc1_unsat_core_size:                   -1
% 19.86/3.01  bmc1_unsat_core_parents_size:           -1
% 19.86/3.01  bmc1_merge_next_fun:                    0
% 19.86/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.86/3.01  
% 19.86/3.01  ------ Instantiation
% 19.86/3.01  
% 19.86/3.01  inst_num_of_clauses:                    3032
% 19.86/3.01  inst_num_in_passive:                    1856
% 19.86/3.01  inst_num_in_active:                     945
% 19.86/3.01  inst_num_in_unprocessed:                232
% 19.86/3.01  inst_num_of_loops:                      970
% 19.86/3.01  inst_num_of_learning_restarts:          0
% 19.86/3.01  inst_num_moves_active_passive:          20
% 19.86/3.01  inst_lit_activity:                      0
% 19.86/3.01  inst_lit_activity_moves:                0
% 19.86/3.01  inst_num_tautologies:                   0
% 19.86/3.01  inst_num_prop_implied:                  0
% 19.86/3.01  inst_num_existing_simplified:           0
% 19.86/3.01  inst_num_eq_res_simplified:             0
% 19.86/3.01  inst_num_child_elim:                    0
% 19.86/3.01  inst_num_of_dismatching_blockings:      2006
% 19.86/3.01  inst_num_of_non_proper_insts:           3319
% 19.86/3.01  inst_num_of_duplicates:                 0
% 19.86/3.01  inst_inst_num_from_inst_to_res:         0
% 19.86/3.01  inst_dismatching_checking_time:         0.
% 19.86/3.01  
% 19.86/3.01  ------ Resolution
% 19.86/3.01  
% 19.86/3.01  res_num_of_clauses:                     0
% 19.86/3.01  res_num_in_passive:                     0
% 19.86/3.01  res_num_in_active:                      0
% 19.86/3.01  res_num_of_loops:                       107
% 19.86/3.01  res_forward_subset_subsumed:            348
% 19.86/3.01  res_backward_subset_subsumed:           6
% 19.86/3.01  res_forward_subsumed:                   0
% 19.86/3.01  res_backward_subsumed:                  0
% 19.86/3.01  res_forward_subsumption_resolution:     2
% 19.86/3.01  res_backward_subsumption_resolution:    0
% 19.86/3.01  res_clause_to_clause_subsumption:       19677
% 19.86/3.01  res_orphan_elimination:                 0
% 19.86/3.01  res_tautology_del:                      500
% 19.86/3.01  res_num_eq_res_simplified:              0
% 19.86/3.01  res_num_sel_changes:                    0
% 19.86/3.01  res_moves_from_active_to_pass:          0
% 19.86/3.01  
% 19.86/3.01  ------ Superposition
% 19.86/3.01  
% 19.86/3.01  sup_time_total:                         0.
% 19.86/3.01  sup_time_generating:                    0.
% 19.86/3.01  sup_time_sim_full:                      0.
% 19.86/3.01  sup_time_sim_immed:                     0.
% 19.86/3.01  
% 19.86/3.01  sup_num_of_clauses:                     1791
% 19.86/3.01  sup_num_in_active:                      184
% 19.86/3.01  sup_num_in_passive:                     1607
% 19.86/3.01  sup_num_of_loops:                       192
% 19.86/3.01  sup_fw_superposition:                   1453
% 19.86/3.01  sup_bw_superposition:                   1108
% 19.86/3.01  sup_immediate_simplified:               1025
% 19.86/3.01  sup_given_eliminated:                   4
% 19.86/3.01  comparisons_done:                       0
% 19.86/3.01  comparisons_avoided:                    0
% 19.86/3.01  
% 19.86/3.01  ------ Simplifications
% 19.86/3.01  
% 19.86/3.01  
% 19.86/3.01  sim_fw_subset_subsumed:                 47
% 19.86/3.01  sim_bw_subset_subsumed:                 6
% 19.86/3.01  sim_fw_subsumed:                        141
% 19.86/3.01  sim_bw_subsumed:                        12
% 19.86/3.01  sim_fw_subsumption_res:                 4
% 19.86/3.01  sim_bw_subsumption_res:                 0
% 19.86/3.01  sim_tautology_del:                      37
% 19.86/3.01  sim_eq_tautology_del:                   74
% 19.86/3.01  sim_eq_res_simp:                        0
% 19.86/3.01  sim_fw_demodulated:                     412
% 19.86/3.01  sim_bw_demodulated:                     69
% 19.86/3.01  sim_light_normalised:                   605
% 19.86/3.01  sim_joinable_taut:                      0
% 19.86/3.01  sim_joinable_simp:                      0
% 19.86/3.01  sim_ac_normalised:                      0
% 19.86/3.01  sim_smt_subsumption:                    0
% 19.86/3.01  
%------------------------------------------------------------------------------
