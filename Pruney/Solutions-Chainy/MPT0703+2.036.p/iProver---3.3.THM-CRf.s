%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:20 EST 2020

% Result     : Theorem 23.69s
% Output     : CNFRefutation 23.69s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 218 expanded)
%              Number of clauses        :   53 (  77 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 ( 742 expanded)
%              Number of equality atoms :   66 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f37,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37])).

fof(f58,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_767,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_765,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2367,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_767,c_765])).

cnf(c_8,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_761,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4118,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_761])).

cnf(c_4119,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4118,c_2367])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_757,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_762,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1347,plain,
    ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_757,c_762])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_280,plain,
    ( r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_281,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_754,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1650,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_754])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_768,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5581,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0)
    | r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_768])).

cnf(c_16,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X1,X2)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X0),X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_303,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X1,X2)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X0),X2)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_304,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,X0),X1))) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_752,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,X0),X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_1566,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_752])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_758,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_243,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_21])).

cnf(c_756,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_1813,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_758,c_756])).

cnf(c_6139,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1566,c_1813])).

cnf(c_99738,plain,
    ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5581,c_6139])).

cnf(c_13,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_260,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_261,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_265,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_21])).

cnf(c_755,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_763,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2838,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_763])).

cnf(c_99816,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),X0) = iProver_top
    | r1_tarski(k3_xboole_0(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_99738,c_2838])).

cnf(c_99998,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_99816,c_1813])).

cnf(c_107484,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4119,c_99998])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107484,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:33:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.69/3.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.69/3.43  
% 23.69/3.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.69/3.43  
% 23.69/3.43  ------  iProver source info
% 23.69/3.43  
% 23.69/3.43  git: date: 2020-06-30 10:37:57 +0100
% 23.69/3.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.69/3.43  git: non_committed_changes: false
% 23.69/3.43  git: last_make_outside_of_git: false
% 23.69/3.43  
% 23.69/3.43  ------ 
% 23.69/3.43  
% 23.69/3.43  ------ Input Options
% 23.69/3.43  
% 23.69/3.43  --out_options                           all
% 23.69/3.43  --tptp_safe_out                         true
% 23.69/3.43  --problem_path                          ""
% 23.69/3.43  --include_path                          ""
% 23.69/3.43  --clausifier                            res/vclausify_rel
% 23.69/3.43  --clausifier_options                    --mode clausify
% 23.69/3.43  --stdin                                 false
% 23.69/3.43  --stats_out                             all
% 23.69/3.43  
% 23.69/3.43  ------ General Options
% 23.69/3.43  
% 23.69/3.43  --fof                                   false
% 23.69/3.43  --time_out_real                         305.
% 23.69/3.43  --time_out_virtual                      -1.
% 23.69/3.43  --symbol_type_check                     false
% 23.69/3.43  --clausify_out                          false
% 23.69/3.43  --sig_cnt_out                           false
% 23.69/3.43  --trig_cnt_out                          false
% 23.69/3.43  --trig_cnt_out_tolerance                1.
% 23.69/3.43  --trig_cnt_out_sk_spl                   false
% 23.69/3.43  --abstr_cl_out                          false
% 23.69/3.43  
% 23.69/3.43  ------ Global Options
% 23.69/3.43  
% 23.69/3.43  --schedule                              default
% 23.69/3.43  --add_important_lit                     false
% 23.69/3.43  --prop_solver_per_cl                    1000
% 23.69/3.43  --min_unsat_core                        false
% 23.69/3.43  --soft_assumptions                      false
% 23.69/3.43  --soft_lemma_size                       3
% 23.69/3.43  --prop_impl_unit_size                   0
% 23.69/3.43  --prop_impl_unit                        []
% 23.69/3.43  --share_sel_clauses                     true
% 23.69/3.43  --reset_solvers                         false
% 23.69/3.43  --bc_imp_inh                            [conj_cone]
% 23.69/3.43  --conj_cone_tolerance                   3.
% 23.69/3.43  --extra_neg_conj                        none
% 23.69/3.43  --large_theory_mode                     true
% 23.69/3.43  --prolific_symb_bound                   200
% 23.69/3.43  --lt_threshold                          2000
% 23.69/3.43  --clause_weak_htbl                      true
% 23.69/3.43  --gc_record_bc_elim                     false
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing Options
% 23.69/3.43  
% 23.69/3.43  --preprocessing_flag                    true
% 23.69/3.43  --time_out_prep_mult                    0.1
% 23.69/3.43  --splitting_mode                        input
% 23.69/3.43  --splitting_grd                         true
% 23.69/3.43  --splitting_cvd                         false
% 23.69/3.43  --splitting_cvd_svl                     false
% 23.69/3.43  --splitting_nvd                         32
% 23.69/3.43  --sub_typing                            true
% 23.69/3.43  --prep_gs_sim                           true
% 23.69/3.43  --prep_unflatten                        true
% 23.69/3.43  --prep_res_sim                          true
% 23.69/3.43  --prep_upred                            true
% 23.69/3.43  --prep_sem_filter                       exhaustive
% 23.69/3.43  --prep_sem_filter_out                   false
% 23.69/3.43  --pred_elim                             true
% 23.69/3.43  --res_sim_input                         true
% 23.69/3.43  --eq_ax_congr_red                       true
% 23.69/3.43  --pure_diseq_elim                       true
% 23.69/3.43  --brand_transform                       false
% 23.69/3.43  --non_eq_to_eq                          false
% 23.69/3.43  --prep_def_merge                        true
% 23.69/3.43  --prep_def_merge_prop_impl              false
% 23.69/3.43  --prep_def_merge_mbd                    true
% 23.69/3.43  --prep_def_merge_tr_red                 false
% 23.69/3.43  --prep_def_merge_tr_cl                  false
% 23.69/3.43  --smt_preprocessing                     true
% 23.69/3.43  --smt_ac_axioms                         fast
% 23.69/3.43  --preprocessed_out                      false
% 23.69/3.43  --preprocessed_stats                    false
% 23.69/3.43  
% 23.69/3.43  ------ Abstraction refinement Options
% 23.69/3.43  
% 23.69/3.43  --abstr_ref                             []
% 23.69/3.43  --abstr_ref_prep                        false
% 23.69/3.43  --abstr_ref_until_sat                   false
% 23.69/3.43  --abstr_ref_sig_restrict                funpre
% 23.69/3.43  --abstr_ref_af_restrict_to_split_sk     false
% 23.69/3.43  --abstr_ref_under                       []
% 23.69/3.43  
% 23.69/3.43  ------ SAT Options
% 23.69/3.43  
% 23.69/3.43  --sat_mode                              false
% 23.69/3.43  --sat_fm_restart_options                ""
% 23.69/3.43  --sat_gr_def                            false
% 23.69/3.43  --sat_epr_types                         true
% 23.69/3.43  --sat_non_cyclic_types                  false
% 23.69/3.43  --sat_finite_models                     false
% 23.69/3.43  --sat_fm_lemmas                         false
% 23.69/3.43  --sat_fm_prep                           false
% 23.69/3.43  --sat_fm_uc_incr                        true
% 23.69/3.43  --sat_out_model                         small
% 23.69/3.43  --sat_out_clauses                       false
% 23.69/3.43  
% 23.69/3.43  ------ QBF Options
% 23.69/3.43  
% 23.69/3.43  --qbf_mode                              false
% 23.69/3.43  --qbf_elim_univ                         false
% 23.69/3.43  --qbf_dom_inst                          none
% 23.69/3.43  --qbf_dom_pre_inst                      false
% 23.69/3.43  --qbf_sk_in                             false
% 23.69/3.43  --qbf_pred_elim                         true
% 23.69/3.43  --qbf_split                             512
% 23.69/3.43  
% 23.69/3.43  ------ BMC1 Options
% 23.69/3.43  
% 23.69/3.43  --bmc1_incremental                      false
% 23.69/3.43  --bmc1_axioms                           reachable_all
% 23.69/3.43  --bmc1_min_bound                        0
% 23.69/3.43  --bmc1_max_bound                        -1
% 23.69/3.43  --bmc1_max_bound_default                -1
% 23.69/3.43  --bmc1_symbol_reachability              true
% 23.69/3.43  --bmc1_property_lemmas                  false
% 23.69/3.43  --bmc1_k_induction                      false
% 23.69/3.43  --bmc1_non_equiv_states                 false
% 23.69/3.43  --bmc1_deadlock                         false
% 23.69/3.43  --bmc1_ucm                              false
% 23.69/3.43  --bmc1_add_unsat_core                   none
% 23.69/3.43  --bmc1_unsat_core_children              false
% 23.69/3.43  --bmc1_unsat_core_extrapolate_axioms    false
% 23.69/3.43  --bmc1_out_stat                         full
% 23.69/3.43  --bmc1_ground_init                      false
% 23.69/3.43  --bmc1_pre_inst_next_state              false
% 23.69/3.43  --bmc1_pre_inst_state                   false
% 23.69/3.43  --bmc1_pre_inst_reach_state             false
% 23.69/3.43  --bmc1_out_unsat_core                   false
% 23.69/3.43  --bmc1_aig_witness_out                  false
% 23.69/3.43  --bmc1_verbose                          false
% 23.69/3.43  --bmc1_dump_clauses_tptp                false
% 23.69/3.43  --bmc1_dump_unsat_core_tptp             false
% 23.69/3.43  --bmc1_dump_file                        -
% 23.69/3.43  --bmc1_ucm_expand_uc_limit              128
% 23.69/3.43  --bmc1_ucm_n_expand_iterations          6
% 23.69/3.43  --bmc1_ucm_extend_mode                  1
% 23.69/3.43  --bmc1_ucm_init_mode                    2
% 23.69/3.43  --bmc1_ucm_cone_mode                    none
% 23.69/3.43  --bmc1_ucm_reduced_relation_type        0
% 23.69/3.43  --bmc1_ucm_relax_model                  4
% 23.69/3.43  --bmc1_ucm_full_tr_after_sat            true
% 23.69/3.43  --bmc1_ucm_expand_neg_assumptions       false
% 23.69/3.43  --bmc1_ucm_layered_model                none
% 23.69/3.43  --bmc1_ucm_max_lemma_size               10
% 23.69/3.43  
% 23.69/3.43  ------ AIG Options
% 23.69/3.43  
% 23.69/3.43  --aig_mode                              false
% 23.69/3.43  
% 23.69/3.43  ------ Instantiation Options
% 23.69/3.43  
% 23.69/3.43  --instantiation_flag                    true
% 23.69/3.43  --inst_sos_flag                         false
% 23.69/3.43  --inst_sos_phase                        true
% 23.69/3.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.69/3.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.69/3.43  --inst_lit_sel_side                     num_symb
% 23.69/3.43  --inst_solver_per_active                1400
% 23.69/3.43  --inst_solver_calls_frac                1.
% 23.69/3.43  --inst_passive_queue_type               priority_queues
% 23.69/3.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.69/3.43  --inst_passive_queues_freq              [25;2]
% 23.69/3.43  --inst_dismatching                      true
% 23.69/3.43  --inst_eager_unprocessed_to_passive     true
% 23.69/3.43  --inst_prop_sim_given                   true
% 23.69/3.43  --inst_prop_sim_new                     false
% 23.69/3.43  --inst_subs_new                         false
% 23.69/3.43  --inst_eq_res_simp                      false
% 23.69/3.43  --inst_subs_given                       false
% 23.69/3.43  --inst_orphan_elimination               true
% 23.69/3.43  --inst_learning_loop_flag               true
% 23.69/3.43  --inst_learning_start                   3000
% 23.69/3.43  --inst_learning_factor                  2
% 23.69/3.43  --inst_start_prop_sim_after_learn       3
% 23.69/3.43  --inst_sel_renew                        solver
% 23.69/3.43  --inst_lit_activity_flag                true
% 23.69/3.43  --inst_restr_to_given                   false
% 23.69/3.43  --inst_activity_threshold               500
% 23.69/3.43  --inst_out_proof                        true
% 23.69/3.43  
% 23.69/3.43  ------ Resolution Options
% 23.69/3.43  
% 23.69/3.43  --resolution_flag                       true
% 23.69/3.43  --res_lit_sel                           adaptive
% 23.69/3.43  --res_lit_sel_side                      none
% 23.69/3.43  --res_ordering                          kbo
% 23.69/3.43  --res_to_prop_solver                    active
% 23.69/3.43  --res_prop_simpl_new                    false
% 23.69/3.43  --res_prop_simpl_given                  true
% 23.69/3.43  --res_passive_queue_type                priority_queues
% 23.69/3.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.69/3.43  --res_passive_queues_freq               [15;5]
% 23.69/3.43  --res_forward_subs                      full
% 23.69/3.43  --res_backward_subs                     full
% 23.69/3.43  --res_forward_subs_resolution           true
% 23.69/3.43  --res_backward_subs_resolution          true
% 23.69/3.43  --res_orphan_elimination                true
% 23.69/3.43  --res_time_limit                        2.
% 23.69/3.43  --res_out_proof                         true
% 23.69/3.43  
% 23.69/3.43  ------ Superposition Options
% 23.69/3.43  
% 23.69/3.43  --superposition_flag                    true
% 23.69/3.43  --sup_passive_queue_type                priority_queues
% 23.69/3.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.69/3.43  --sup_passive_queues_freq               [8;1;4]
% 23.69/3.43  --demod_completeness_check              fast
% 23.69/3.43  --demod_use_ground                      true
% 23.69/3.43  --sup_to_prop_solver                    passive
% 23.69/3.43  --sup_prop_simpl_new                    true
% 23.69/3.43  --sup_prop_simpl_given                  true
% 23.69/3.43  --sup_fun_splitting                     false
% 23.69/3.43  --sup_smt_interval                      50000
% 23.69/3.43  
% 23.69/3.43  ------ Superposition Simplification Setup
% 23.69/3.43  
% 23.69/3.43  --sup_indices_passive                   []
% 23.69/3.43  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_full_triv                         [TrivRules;PropSubs]
% 23.69/3.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_full_bw                           [BwDemod]
% 23.69/3.43  --sup_immed_triv                        [TrivRules]
% 23.69/3.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.69/3.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_immed_bw_main                     []
% 23.69/3.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.69/3.43  --sup_input_triv                        [Unflattening;TrivRules]
% 23.69/3.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.69/3.43  
% 23.69/3.43  ------ Combination Options
% 23.69/3.43  
% 23.69/3.43  --comb_res_mult                         3
% 23.69/3.43  --comb_sup_mult                         2
% 23.69/3.43  --comb_inst_mult                        10
% 23.69/3.43  
% 23.69/3.43  ------ Debug Options
% 23.69/3.43  
% 23.69/3.43  --dbg_backtrace                         false
% 23.69/3.43  --dbg_dump_prop_clauses                 false
% 23.69/3.43  --dbg_dump_prop_clauses_file            -
% 23.69/3.43  --dbg_out_stat                          false
% 23.69/3.43  ------ Parsing...
% 23.69/3.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.69/3.43  ------ Proving...
% 23.69/3.43  ------ Problem Properties 
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  clauses                                 19
% 23.69/3.43  conjectures                             3
% 23.69/3.43  EPR                                     4
% 23.69/3.43  Horn                                    19
% 23.69/3.43  unary                                   12
% 23.69/3.43  binary                                  5
% 23.69/3.43  lits                                    28
% 23.69/3.43  lits eq                                 5
% 23.69/3.43  fd_pure                                 0
% 23.69/3.43  fd_pseudo                               0
% 23.69/3.43  fd_cond                                 0
% 23.69/3.43  fd_pseudo_cond                          1
% 23.69/3.43  AC symbols                              0
% 23.69/3.43  
% 23.69/3.43  ------ Schedule dynamic 5 is on 
% 23.69/3.43  
% 23.69/3.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  ------ 
% 23.69/3.43  Current options:
% 23.69/3.43  ------ 
% 23.69/3.43  
% 23.69/3.43  ------ Input Options
% 23.69/3.43  
% 23.69/3.43  --out_options                           all
% 23.69/3.43  --tptp_safe_out                         true
% 23.69/3.43  --problem_path                          ""
% 23.69/3.43  --include_path                          ""
% 23.69/3.43  --clausifier                            res/vclausify_rel
% 23.69/3.43  --clausifier_options                    --mode clausify
% 23.69/3.43  --stdin                                 false
% 23.69/3.43  --stats_out                             all
% 23.69/3.43  
% 23.69/3.43  ------ General Options
% 23.69/3.43  
% 23.69/3.43  --fof                                   false
% 23.69/3.43  --time_out_real                         305.
% 23.69/3.43  --time_out_virtual                      -1.
% 23.69/3.43  --symbol_type_check                     false
% 23.69/3.43  --clausify_out                          false
% 23.69/3.43  --sig_cnt_out                           false
% 23.69/3.43  --trig_cnt_out                          false
% 23.69/3.43  --trig_cnt_out_tolerance                1.
% 23.69/3.43  --trig_cnt_out_sk_spl                   false
% 23.69/3.43  --abstr_cl_out                          false
% 23.69/3.43  
% 23.69/3.43  ------ Global Options
% 23.69/3.43  
% 23.69/3.43  --schedule                              default
% 23.69/3.43  --add_important_lit                     false
% 23.69/3.43  --prop_solver_per_cl                    1000
% 23.69/3.43  --min_unsat_core                        false
% 23.69/3.43  --soft_assumptions                      false
% 23.69/3.43  --soft_lemma_size                       3
% 23.69/3.43  --prop_impl_unit_size                   0
% 23.69/3.43  --prop_impl_unit                        []
% 23.69/3.43  --share_sel_clauses                     true
% 23.69/3.43  --reset_solvers                         false
% 23.69/3.43  --bc_imp_inh                            [conj_cone]
% 23.69/3.43  --conj_cone_tolerance                   3.
% 23.69/3.43  --extra_neg_conj                        none
% 23.69/3.43  --large_theory_mode                     true
% 23.69/3.43  --prolific_symb_bound                   200
% 23.69/3.43  --lt_threshold                          2000
% 23.69/3.43  --clause_weak_htbl                      true
% 23.69/3.43  --gc_record_bc_elim                     false
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing Options
% 23.69/3.43  
% 23.69/3.43  --preprocessing_flag                    true
% 23.69/3.43  --time_out_prep_mult                    0.1
% 23.69/3.43  --splitting_mode                        input
% 23.69/3.43  --splitting_grd                         true
% 23.69/3.43  --splitting_cvd                         false
% 23.69/3.43  --splitting_cvd_svl                     false
% 23.69/3.43  --splitting_nvd                         32
% 23.69/3.43  --sub_typing                            true
% 23.69/3.43  --prep_gs_sim                           true
% 23.69/3.43  --prep_unflatten                        true
% 23.69/3.43  --prep_res_sim                          true
% 23.69/3.43  --prep_upred                            true
% 23.69/3.43  --prep_sem_filter                       exhaustive
% 23.69/3.43  --prep_sem_filter_out                   false
% 23.69/3.43  --pred_elim                             true
% 23.69/3.43  --res_sim_input                         true
% 23.69/3.43  --eq_ax_congr_red                       true
% 23.69/3.43  --pure_diseq_elim                       true
% 23.69/3.43  --brand_transform                       false
% 23.69/3.43  --non_eq_to_eq                          false
% 23.69/3.43  --prep_def_merge                        true
% 23.69/3.43  --prep_def_merge_prop_impl              false
% 23.69/3.43  --prep_def_merge_mbd                    true
% 23.69/3.43  --prep_def_merge_tr_red                 false
% 23.69/3.43  --prep_def_merge_tr_cl                  false
% 23.69/3.43  --smt_preprocessing                     true
% 23.69/3.43  --smt_ac_axioms                         fast
% 23.69/3.43  --preprocessed_out                      false
% 23.69/3.43  --preprocessed_stats                    false
% 23.69/3.43  
% 23.69/3.43  ------ Abstraction refinement Options
% 23.69/3.43  
% 23.69/3.43  --abstr_ref                             []
% 23.69/3.43  --abstr_ref_prep                        false
% 23.69/3.43  --abstr_ref_until_sat                   false
% 23.69/3.43  --abstr_ref_sig_restrict                funpre
% 23.69/3.43  --abstr_ref_af_restrict_to_split_sk     false
% 23.69/3.43  --abstr_ref_under                       []
% 23.69/3.43  
% 23.69/3.43  ------ SAT Options
% 23.69/3.43  
% 23.69/3.43  --sat_mode                              false
% 23.69/3.43  --sat_fm_restart_options                ""
% 23.69/3.43  --sat_gr_def                            false
% 23.69/3.43  --sat_epr_types                         true
% 23.69/3.43  --sat_non_cyclic_types                  false
% 23.69/3.43  --sat_finite_models                     false
% 23.69/3.43  --sat_fm_lemmas                         false
% 23.69/3.43  --sat_fm_prep                           false
% 23.69/3.43  --sat_fm_uc_incr                        true
% 23.69/3.43  --sat_out_model                         small
% 23.69/3.43  --sat_out_clauses                       false
% 23.69/3.43  
% 23.69/3.43  ------ QBF Options
% 23.69/3.43  
% 23.69/3.43  --qbf_mode                              false
% 23.69/3.43  --qbf_elim_univ                         false
% 23.69/3.43  --qbf_dom_inst                          none
% 23.69/3.43  --qbf_dom_pre_inst                      false
% 23.69/3.43  --qbf_sk_in                             false
% 23.69/3.43  --qbf_pred_elim                         true
% 23.69/3.43  --qbf_split                             512
% 23.69/3.43  
% 23.69/3.43  ------ BMC1 Options
% 23.69/3.43  
% 23.69/3.43  --bmc1_incremental                      false
% 23.69/3.43  --bmc1_axioms                           reachable_all
% 23.69/3.43  --bmc1_min_bound                        0
% 23.69/3.43  --bmc1_max_bound                        -1
% 23.69/3.43  --bmc1_max_bound_default                -1
% 23.69/3.43  --bmc1_symbol_reachability              true
% 23.69/3.43  --bmc1_property_lemmas                  false
% 23.69/3.43  --bmc1_k_induction                      false
% 23.69/3.43  --bmc1_non_equiv_states                 false
% 23.69/3.43  --bmc1_deadlock                         false
% 23.69/3.43  --bmc1_ucm                              false
% 23.69/3.43  --bmc1_add_unsat_core                   none
% 23.69/3.43  --bmc1_unsat_core_children              false
% 23.69/3.43  --bmc1_unsat_core_extrapolate_axioms    false
% 23.69/3.43  --bmc1_out_stat                         full
% 23.69/3.43  --bmc1_ground_init                      false
% 23.69/3.43  --bmc1_pre_inst_next_state              false
% 23.69/3.43  --bmc1_pre_inst_state                   false
% 23.69/3.43  --bmc1_pre_inst_reach_state             false
% 23.69/3.43  --bmc1_out_unsat_core                   false
% 23.69/3.43  --bmc1_aig_witness_out                  false
% 23.69/3.43  --bmc1_verbose                          false
% 23.69/3.43  --bmc1_dump_clauses_tptp                false
% 23.69/3.43  --bmc1_dump_unsat_core_tptp             false
% 23.69/3.43  --bmc1_dump_file                        -
% 23.69/3.43  --bmc1_ucm_expand_uc_limit              128
% 23.69/3.43  --bmc1_ucm_n_expand_iterations          6
% 23.69/3.43  --bmc1_ucm_extend_mode                  1
% 23.69/3.43  --bmc1_ucm_init_mode                    2
% 23.69/3.43  --bmc1_ucm_cone_mode                    none
% 23.69/3.43  --bmc1_ucm_reduced_relation_type        0
% 23.69/3.43  --bmc1_ucm_relax_model                  4
% 23.69/3.43  --bmc1_ucm_full_tr_after_sat            true
% 23.69/3.43  --bmc1_ucm_expand_neg_assumptions       false
% 23.69/3.43  --bmc1_ucm_layered_model                none
% 23.69/3.43  --bmc1_ucm_max_lemma_size               10
% 23.69/3.43  
% 23.69/3.43  ------ AIG Options
% 23.69/3.43  
% 23.69/3.43  --aig_mode                              false
% 23.69/3.43  
% 23.69/3.43  ------ Instantiation Options
% 23.69/3.43  
% 23.69/3.43  --instantiation_flag                    true
% 23.69/3.43  --inst_sos_flag                         false
% 23.69/3.43  --inst_sos_phase                        true
% 23.69/3.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.69/3.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.69/3.43  --inst_lit_sel_side                     none
% 23.69/3.43  --inst_solver_per_active                1400
% 23.69/3.43  --inst_solver_calls_frac                1.
% 23.69/3.43  --inst_passive_queue_type               priority_queues
% 23.69/3.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.69/3.43  --inst_passive_queues_freq              [25;2]
% 23.69/3.43  --inst_dismatching                      true
% 23.69/3.43  --inst_eager_unprocessed_to_passive     true
% 23.69/3.43  --inst_prop_sim_given                   true
% 23.69/3.43  --inst_prop_sim_new                     false
% 23.69/3.43  --inst_subs_new                         false
% 23.69/3.43  --inst_eq_res_simp                      false
% 23.69/3.43  --inst_subs_given                       false
% 23.69/3.43  --inst_orphan_elimination               true
% 23.69/3.43  --inst_learning_loop_flag               true
% 23.69/3.43  --inst_learning_start                   3000
% 23.69/3.43  --inst_learning_factor                  2
% 23.69/3.43  --inst_start_prop_sim_after_learn       3
% 23.69/3.43  --inst_sel_renew                        solver
% 23.69/3.43  --inst_lit_activity_flag                true
% 23.69/3.43  --inst_restr_to_given                   false
% 23.69/3.43  --inst_activity_threshold               500
% 23.69/3.43  --inst_out_proof                        true
% 23.69/3.43  
% 23.69/3.43  ------ Resolution Options
% 23.69/3.43  
% 23.69/3.43  --resolution_flag                       false
% 23.69/3.43  --res_lit_sel                           adaptive
% 23.69/3.43  --res_lit_sel_side                      none
% 23.69/3.43  --res_ordering                          kbo
% 23.69/3.43  --res_to_prop_solver                    active
% 23.69/3.43  --res_prop_simpl_new                    false
% 23.69/3.43  --res_prop_simpl_given                  true
% 23.69/3.43  --res_passive_queue_type                priority_queues
% 23.69/3.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.69/3.43  --res_passive_queues_freq               [15;5]
% 23.69/3.43  --res_forward_subs                      full
% 23.69/3.43  --res_backward_subs                     full
% 23.69/3.43  --res_forward_subs_resolution           true
% 23.69/3.43  --res_backward_subs_resolution          true
% 23.69/3.43  --res_orphan_elimination                true
% 23.69/3.43  --res_time_limit                        2.
% 23.69/3.43  --res_out_proof                         true
% 23.69/3.43  
% 23.69/3.43  ------ Superposition Options
% 23.69/3.43  
% 23.69/3.43  --superposition_flag                    true
% 23.69/3.43  --sup_passive_queue_type                priority_queues
% 23.69/3.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.69/3.43  --sup_passive_queues_freq               [8;1;4]
% 23.69/3.43  --demod_completeness_check              fast
% 23.69/3.43  --demod_use_ground                      true
% 23.69/3.43  --sup_to_prop_solver                    passive
% 23.69/3.43  --sup_prop_simpl_new                    true
% 23.69/3.43  --sup_prop_simpl_given                  true
% 23.69/3.43  --sup_fun_splitting                     false
% 23.69/3.43  --sup_smt_interval                      50000
% 23.69/3.43  
% 23.69/3.43  ------ Superposition Simplification Setup
% 23.69/3.43  
% 23.69/3.43  --sup_indices_passive                   []
% 23.69/3.43  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.69/3.43  --sup_full_triv                         [TrivRules;PropSubs]
% 23.69/3.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_full_bw                           [BwDemod]
% 23.69/3.43  --sup_immed_triv                        [TrivRules]
% 23.69/3.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.69/3.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_immed_bw_main                     []
% 23.69/3.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.69/3.43  --sup_input_triv                        [Unflattening;TrivRules]
% 23.69/3.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.69/3.43  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.69/3.43  
% 23.69/3.43  ------ Combination Options
% 23.69/3.43  
% 23.69/3.43  --comb_res_mult                         3
% 23.69/3.43  --comb_sup_mult                         2
% 23.69/3.43  --comb_inst_mult                        10
% 23.69/3.43  
% 23.69/3.43  ------ Debug Options
% 23.69/3.43  
% 23.69/3.43  --dbg_backtrace                         false
% 23.69/3.43  --dbg_dump_prop_clauses                 false
% 23.69/3.43  --dbg_dump_prop_clauses_file            -
% 23.69/3.43  --dbg_out_stat                          false
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  ------ Proving...
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  % SZS status Theorem for theBenchmark.p
% 23.69/3.43  
% 23.69/3.43  % SZS output start CNFRefutation for theBenchmark.p
% 23.69/3.43  
% 23.69/3.43  fof(f1,axiom,(
% 23.69/3.43    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f35,plain,(
% 23.69/3.43    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.69/3.43    inference(nnf_transformation,[],[f1])).
% 23.69/3.43  
% 23.69/3.43  fof(f36,plain,(
% 23.69/3.43    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.69/3.43    inference(flattening,[],[f35])).
% 23.69/3.43  
% 23.69/3.43  fof(f40,plain,(
% 23.69/3.43    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.69/3.43    inference(cnf_transformation,[],[f36])).
% 23.69/3.43  
% 23.69/3.43  fof(f61,plain,(
% 23.69/3.43    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.69/3.43    inference(equality_resolution,[],[f40])).
% 23.69/3.43  
% 23.69/3.43  fof(f3,axiom,(
% 23.69/3.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f19,plain,(
% 23.69/3.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 23.69/3.43    inference(ennf_transformation,[],[f3])).
% 23.69/3.43  
% 23.69/3.43  fof(f43,plain,(
% 23.69/3.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f19])).
% 23.69/3.43  
% 23.69/3.43  fof(f7,axiom,(
% 23.69/3.43    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f47,plain,(
% 23.69/3.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 23.69/3.43    inference(cnf_transformation,[],[f7])).
% 23.69/3.43  
% 23.69/3.43  fof(f16,conjecture,(
% 23.69/3.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f17,negated_conjecture,(
% 23.69/3.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.69/3.43    inference(negated_conjecture,[],[f16])).
% 23.69/3.43  
% 23.69/3.43  fof(f33,plain,(
% 23.69/3.43    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 23.69/3.43    inference(ennf_transformation,[],[f17])).
% 23.69/3.43  
% 23.69/3.43  fof(f34,plain,(
% 23.69/3.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 23.69/3.43    inference(flattening,[],[f33])).
% 23.69/3.43  
% 23.69/3.43  fof(f37,plain,(
% 23.69/3.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 23.69/3.43    introduced(choice_axiom,[])).
% 23.69/3.43  
% 23.69/3.43  fof(f38,plain,(
% 23.69/3.43    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 23.69/3.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37])).
% 23.69/3.43  
% 23.69/3.43  fof(f58,plain,(
% 23.69/3.43    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 23.69/3.43    inference(cnf_transformation,[],[f38])).
% 23.69/3.43  
% 23.69/3.43  fof(f6,axiom,(
% 23.69/3.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f22,plain,(
% 23.69/3.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.69/3.43    inference(ennf_transformation,[],[f6])).
% 23.69/3.43  
% 23.69/3.43  fof(f46,plain,(
% 23.69/3.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f22])).
% 23.69/3.43  
% 23.69/3.43  fof(f11,axiom,(
% 23.69/3.43    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f25,plain,(
% 23.69/3.43    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 23.69/3.43    inference(ennf_transformation,[],[f11])).
% 23.69/3.43  
% 23.69/3.43  fof(f51,plain,(
% 23.69/3.43    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f25])).
% 23.69/3.43  
% 23.69/3.43  fof(f56,plain,(
% 23.69/3.43    v1_relat_1(sK2)),
% 23.69/3.43    inference(cnf_transformation,[],[f38])).
% 23.69/3.43  
% 23.69/3.43  fof(f41,plain,(
% 23.69/3.43    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f36])).
% 23.69/3.43  
% 23.69/3.43  fof(f15,axiom,(
% 23.69/3.43    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f32,plain,(
% 23.69/3.43    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2))),
% 23.69/3.43    inference(ennf_transformation,[],[f15])).
% 23.69/3.43  
% 23.69/3.43  fof(f55,plain,(
% 23.69/3.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f32])).
% 23.69/3.43  
% 23.69/3.43  fof(f59,plain,(
% 23.69/3.43    r1_tarski(sK0,k2_relat_1(sK2))),
% 23.69/3.43    inference(cnf_transformation,[],[f38])).
% 23.69/3.43  
% 23.69/3.43  fof(f14,axiom,(
% 23.69/3.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f30,plain,(
% 23.69/3.43    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.69/3.43    inference(ennf_transformation,[],[f14])).
% 23.69/3.43  
% 23.69/3.43  fof(f31,plain,(
% 23.69/3.43    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.69/3.43    inference(flattening,[],[f30])).
% 23.69/3.43  
% 23.69/3.43  fof(f54,plain,(
% 23.69/3.43    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f31])).
% 23.69/3.43  
% 23.69/3.43  fof(f57,plain,(
% 23.69/3.43    v1_funct_1(sK2)),
% 23.69/3.43    inference(cnf_transformation,[],[f38])).
% 23.69/3.43  
% 23.69/3.43  fof(f12,axiom,(
% 23.69/3.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f26,plain,(
% 23.69/3.43    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.69/3.43    inference(ennf_transformation,[],[f12])).
% 23.69/3.43  
% 23.69/3.43  fof(f27,plain,(
% 23.69/3.43    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.69/3.43    inference(flattening,[],[f26])).
% 23.69/3.43  
% 23.69/3.43  fof(f52,plain,(
% 23.69/3.43    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f27])).
% 23.69/3.43  
% 23.69/3.43  fof(f5,axiom,(
% 23.69/3.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 23.69/3.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.69/3.43  
% 23.69/3.43  fof(f20,plain,(
% 23.69/3.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 23.69/3.43    inference(ennf_transformation,[],[f5])).
% 23.69/3.43  
% 23.69/3.43  fof(f21,plain,(
% 23.69/3.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 23.69/3.43    inference(flattening,[],[f20])).
% 23.69/3.43  
% 23.69/3.43  fof(f45,plain,(
% 23.69/3.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 23.69/3.43    inference(cnf_transformation,[],[f21])).
% 23.69/3.43  
% 23.69/3.43  fof(f60,plain,(
% 23.69/3.43    ~r1_tarski(sK0,sK1)),
% 23.69/3.43    inference(cnf_transformation,[],[f38])).
% 23.69/3.43  
% 23.69/3.43  cnf(c_1,plain,
% 23.69/3.43      ( r1_tarski(X0,X0) ),
% 23.69/3.43      inference(cnf_transformation,[],[f61]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_767,plain,
% 23.69/3.43      ( r1_tarski(X0,X0) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_4,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 23.69/3.43      inference(cnf_transformation,[],[f43]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_765,plain,
% 23.69/3.43      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_2367,plain,
% 23.69/3.43      ( k2_xboole_0(X0,X0) = X0 ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_767,c_765]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_8,plain,
% 23.69/3.43      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 23.69/3.43      inference(cnf_transformation,[],[f47]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_761,plain,
% 23.69/3.43      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_4118,plain,
% 23.69/3.43      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_2367,c_761]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_4119,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 23.69/3.43      inference(demodulation,[status(thm)],[c_4118,c_2367]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_19,negated_conjecture,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 23.69/3.43      inference(cnf_transformation,[],[f58]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_757,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_7,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.69/3.43      inference(cnf_transformation,[],[f46]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_762,plain,
% 23.69/3.43      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_1347,plain,
% 23.69/3.43      ( k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_757,c_762]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_12,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)))
% 23.69/3.43      | ~ v1_relat_1(X0) ),
% 23.69/3.43      inference(cnf_transformation,[],[f51]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_21,negated_conjecture,
% 23.69/3.43      ( v1_relat_1(sK2) ),
% 23.69/3.43      inference(cnf_transformation,[],[f56]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_280,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)))
% 23.69/3.43      | sK2 != X0 ),
% 23.69/3.43      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_281,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ),
% 23.69/3.43      inference(unflattening,[status(thm)],[c_280]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_754,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_1650,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) = iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_1347,c_754]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_0,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.69/3.43      inference(cnf_transformation,[],[f41]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_768,plain,
% 23.69/3.43      ( X0 = X1
% 23.69/3.43      | r1_tarski(X0,X1) != iProver_top
% 23.69/3.43      | r1_tarski(X1,X0) != iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_5581,plain,
% 23.69/3.43      ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0)
% 23.69/3.43      | r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) != iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_1650,c_768]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_16,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X1,X2)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X0),X2)))
% 23.69/3.43      | ~ v1_relat_1(X1) ),
% 23.69/3.43      inference(cnf_transformation,[],[f55]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_303,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X1,X2)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X0),X2)))
% 23.69/3.43      | sK2 != X1 ),
% 23.69/3.43      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_304,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,X0),X1))) ),
% 23.69/3.43      inference(unflattening,[status(thm)],[c_303]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_752,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,X0),X1))) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_1566,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))) = iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_1347,c_752]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_18,negated_conjecture,
% 23.69/3.43      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 23.69/3.43      inference(cnf_transformation,[],[f59]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_758,plain,
% 23.69/3.43      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_15,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 23.69/3.43      | ~ v1_funct_1(X1)
% 23.69/3.43      | ~ v1_relat_1(X1)
% 23.69/3.43      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 23.69/3.43      inference(cnf_transformation,[],[f54]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_20,negated_conjecture,
% 23.69/3.43      ( v1_funct_1(sK2) ),
% 23.69/3.43      inference(cnf_transformation,[],[f57]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_242,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 23.69/3.43      | ~ v1_relat_1(X1)
% 23.69/3.43      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 23.69/3.43      | sK2 != X1 ),
% 23.69/3.43      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_243,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 23.69/3.43      | ~ v1_relat_1(sK2)
% 23.69/3.43      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 23.69/3.43      inference(unflattening,[status(thm)],[c_242]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_247,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 23.69/3.43      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 23.69/3.43      inference(global_propositional_subsumption,
% 23.69/3.43                [status(thm)],
% 23.69/3.43                [c_243,c_21]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_756,plain,
% 23.69/3.43      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 23.69/3.43      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_1813,plain,
% 23.69/3.43      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_758,c_756]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_6139,plain,
% 23.69/3.43      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) = iProver_top ),
% 23.69/3.43      inference(light_normalisation,[status(thm)],[c_1566,c_1813]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_99738,plain,
% 23.69/3.43      ( k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) = k10_relat_1(sK2,sK0) ),
% 23.69/3.43      inference(global_propositional_subsumption,
% 23.69/3.43                [status(thm)],
% 23.69/3.43                [c_5581,c_6139]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_13,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 23.69/3.43      | ~ v1_funct_1(X0)
% 23.69/3.43      | ~ v1_relat_1(X0) ),
% 23.69/3.43      inference(cnf_transformation,[],[f52]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_260,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 23.69/3.43      | ~ v1_relat_1(X0)
% 23.69/3.43      | sK2 != X0 ),
% 23.69/3.43      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_261,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 23.69/3.43      | ~ v1_relat_1(sK2) ),
% 23.69/3.43      inference(unflattening,[status(thm)],[c_260]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_265,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 23.69/3.43      inference(global_propositional_subsumption,
% 23.69/3.43                [status(thm)],
% 23.69/3.43                [c_261,c_21]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_755,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_6,plain,
% 23.69/3.43      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 23.69/3.43      inference(cnf_transformation,[],[f45]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_763,plain,
% 23.69/3.43      ( r1_tarski(X0,X1) != iProver_top
% 23.69/3.43      | r1_tarski(X1,X2) != iProver_top
% 23.69/3.43      | r1_tarski(X0,X2) = iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_2838,plain,
% 23.69/3.43      ( r1_tarski(X0,X1) != iProver_top
% 23.69/3.43      | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X1) = iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_755,c_763]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_99816,plain,
% 23.69/3.43      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),X0) = iProver_top
% 23.69/3.43      | r1_tarski(k3_xboole_0(sK0,sK1),X0) != iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_99738,c_2838]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_99998,plain,
% 23.69/3.43      ( r1_tarski(k3_xboole_0(sK0,sK1),X0) != iProver_top
% 23.69/3.43      | r1_tarski(sK0,X0) = iProver_top ),
% 23.69/3.43      inference(light_normalisation,[status(thm)],[c_99816,c_1813]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_107484,plain,
% 23.69/3.43      ( r1_tarski(sK0,sK1) = iProver_top ),
% 23.69/3.43      inference(superposition,[status(thm)],[c_4119,c_99998]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_17,negated_conjecture,
% 23.69/3.43      ( ~ r1_tarski(sK0,sK1) ),
% 23.69/3.43      inference(cnf_transformation,[],[f60]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(c_26,plain,
% 23.69/3.43      ( r1_tarski(sK0,sK1) != iProver_top ),
% 23.69/3.43      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.69/3.43  
% 23.69/3.43  cnf(contradiction,plain,
% 23.69/3.43      ( $false ),
% 23.69/3.43      inference(minisat,[status(thm)],[c_107484,c_26]) ).
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  % SZS output end CNFRefutation for theBenchmark.p
% 23.69/3.43  
% 23.69/3.43  ------                               Statistics
% 23.69/3.43  
% 23.69/3.43  ------ General
% 23.69/3.43  
% 23.69/3.43  abstr_ref_over_cycles:                  0
% 23.69/3.43  abstr_ref_under_cycles:                 0
% 23.69/3.43  gc_basic_clause_elim:                   0
% 23.69/3.43  forced_gc_time:                         0
% 23.69/3.43  parsing_time:                           0.008
% 23.69/3.43  unif_index_cands_time:                  0.
% 23.69/3.43  unif_index_add_time:                    0.
% 23.69/3.43  orderings_time:                         0.
% 23.69/3.43  out_proof_time:                         0.018
% 23.69/3.43  total_time:                             2.855
% 23.69/3.43  num_of_symbols:                         44
% 23.69/3.43  num_of_terms:                           133097
% 23.69/3.43  
% 23.69/3.43  ------ Preprocessing
% 23.69/3.43  
% 23.69/3.43  num_of_splits:                          0
% 23.69/3.43  num_of_split_atoms:                     0
% 23.69/3.43  num_of_reused_defs:                     0
% 23.69/3.43  num_eq_ax_congr_red:                    8
% 23.69/3.43  num_of_sem_filtered_clauses:            1
% 23.69/3.43  num_of_subtypes:                        0
% 23.69/3.43  monotx_restored_types:                  0
% 23.69/3.43  sat_num_of_epr_types:                   0
% 23.69/3.43  sat_num_of_non_cyclic_types:            0
% 23.69/3.43  sat_guarded_non_collapsed_types:        0
% 23.69/3.43  num_pure_diseq_elim:                    0
% 23.69/3.43  simp_replaced_by:                       0
% 23.69/3.43  res_preprocessed:                       97
% 23.69/3.43  prep_upred:                             0
% 23.69/3.43  prep_unflattend:                        7
% 23.69/3.43  smt_new_axioms:                         0
% 23.69/3.43  pred_elim_cands:                        1
% 23.69/3.43  pred_elim:                              2
% 23.69/3.43  pred_elim_cl:                           2
% 23.69/3.43  pred_elim_cycles:                       4
% 23.69/3.43  merged_defs:                            0
% 23.69/3.43  merged_defs_ncl:                        0
% 23.69/3.43  bin_hyper_res:                          0
% 23.69/3.43  prep_cycles:                            4
% 23.69/3.43  pred_elim_time:                         0.002
% 23.69/3.43  splitting_time:                         0.
% 23.69/3.43  sem_filter_time:                        0.
% 23.69/3.43  monotx_time:                            0.
% 23.69/3.43  subtype_inf_time:                       0.
% 23.69/3.43  
% 23.69/3.43  ------ Problem properties
% 23.69/3.43  
% 23.69/3.43  clauses:                                19
% 23.69/3.43  conjectures:                            3
% 23.69/3.43  epr:                                    4
% 23.69/3.43  horn:                                   19
% 23.69/3.43  ground:                                 4
% 23.69/3.43  unary:                                  12
% 23.69/3.43  binary:                                 5
% 23.69/3.43  lits:                                   28
% 23.69/3.43  lits_eq:                                5
% 23.69/3.43  fd_pure:                                0
% 23.69/3.43  fd_pseudo:                              0
% 23.69/3.43  fd_cond:                                0
% 23.69/3.43  fd_pseudo_cond:                         1
% 23.69/3.43  ac_symbols:                             0
% 23.69/3.43  
% 23.69/3.43  ------ Propositional Solver
% 23.69/3.43  
% 23.69/3.43  prop_solver_calls:                      45
% 23.69/3.43  prop_fast_solver_calls:                 961
% 23.69/3.43  smt_solver_calls:                       0
% 23.69/3.43  smt_fast_solver_calls:                  0
% 23.69/3.43  prop_num_of_clauses:                    44910
% 23.69/3.43  prop_preprocess_simplified:             46762
% 23.69/3.43  prop_fo_subsumed:                       5
% 23.69/3.43  prop_solver_time:                       0.
% 23.69/3.43  smt_solver_time:                        0.
% 23.69/3.43  smt_fast_solver_time:                   0.
% 23.69/3.43  prop_fast_solver_time:                  0.
% 23.69/3.43  prop_unsat_core_time:                   0.005
% 23.69/3.43  
% 23.69/3.43  ------ QBF
% 23.69/3.43  
% 23.69/3.43  qbf_q_res:                              0
% 23.69/3.43  qbf_num_tautologies:                    0
% 23.69/3.43  qbf_prep_cycles:                        0
% 23.69/3.43  
% 23.69/3.43  ------ BMC1
% 23.69/3.43  
% 23.69/3.43  bmc1_current_bound:                     -1
% 23.69/3.43  bmc1_last_solved_bound:                 -1
% 23.69/3.43  bmc1_unsat_core_size:                   -1
% 23.69/3.43  bmc1_unsat_core_parents_size:           -1
% 23.69/3.43  bmc1_merge_next_fun:                    0
% 23.69/3.43  bmc1_unsat_core_clauses_time:           0.
% 23.69/3.43  
% 23.69/3.43  ------ Instantiation
% 23.69/3.43  
% 23.69/3.43  inst_num_of_clauses:                    7171
% 23.69/3.43  inst_num_in_passive:                    2381
% 23.69/3.43  inst_num_in_active:                     2243
% 23.69/3.43  inst_num_in_unprocessed:                2548
% 23.69/3.43  inst_num_of_loops:                      2280
% 23.69/3.43  inst_num_of_learning_restarts:          0
% 23.69/3.43  inst_num_moves_active_passive:          35
% 23.69/3.43  inst_lit_activity:                      0
% 23.69/3.43  inst_lit_activity_moves:                1
% 23.69/3.43  inst_num_tautologies:                   0
% 23.69/3.43  inst_num_prop_implied:                  0
% 23.69/3.43  inst_num_existing_simplified:           0
% 23.69/3.43  inst_num_eq_res_simplified:             0
% 23.69/3.43  inst_num_child_elim:                    0
% 23.69/3.43  inst_num_of_dismatching_blockings:      1976
% 23.69/3.43  inst_num_of_non_proper_insts:           6960
% 23.69/3.43  inst_num_of_duplicates:                 0
% 23.69/3.43  inst_inst_num_from_inst_to_res:         0
% 23.69/3.43  inst_dismatching_checking_time:         0.
% 23.69/3.43  
% 23.69/3.43  ------ Resolution
% 23.69/3.43  
% 23.69/3.43  res_num_of_clauses:                     0
% 23.69/3.43  res_num_in_passive:                     0
% 23.69/3.43  res_num_in_active:                      0
% 23.69/3.43  res_num_of_loops:                       101
% 23.69/3.43  res_forward_subset_subsumed:            397
% 23.69/3.43  res_backward_subset_subsumed:           6
% 23.69/3.43  res_forward_subsumed:                   0
% 23.69/3.43  res_backward_subsumed:                  0
% 23.69/3.43  res_forward_subsumption_resolution:     0
% 23.69/3.43  res_backward_subsumption_resolution:    0
% 23.69/3.43  res_clause_to_clause_subsumption:       55244
% 23.69/3.43  res_orphan_elimination:                 0
% 23.69/3.43  res_tautology_del:                      762
% 23.69/3.43  res_num_eq_res_simplified:              0
% 23.69/3.43  res_num_sel_changes:                    0
% 23.69/3.43  res_moves_from_active_to_pass:          0
% 23.69/3.43  
% 23.69/3.43  ------ Superposition
% 23.69/3.43  
% 23.69/3.43  sup_time_total:                         0.
% 23.69/3.43  sup_time_generating:                    0.
% 23.69/3.43  sup_time_sim_full:                      0.
% 23.69/3.43  sup_time_sim_immed:                     0.
% 23.69/3.43  
% 23.69/3.43  sup_num_of_clauses:                     7174
% 23.69/3.43  sup_num_in_active:                      360
% 23.69/3.43  sup_num_in_passive:                     6814
% 23.69/3.43  sup_num_of_loops:                       454
% 23.69/3.43  sup_fw_superposition:                   10335
% 23.69/3.43  sup_bw_superposition:                   8711
% 23.69/3.43  sup_immediate_simplified:               7188
% 23.69/3.43  sup_given_eliminated:                   44
% 23.69/3.43  comparisons_done:                       0
% 23.69/3.43  comparisons_avoided:                    0
% 23.69/3.43  
% 23.69/3.43  ------ Simplifications
% 23.69/3.43  
% 23.69/3.43  
% 23.69/3.43  sim_fw_subset_subsumed:                 201
% 23.69/3.43  sim_bw_subset_subsumed:                 55
% 23.69/3.43  sim_fw_subsumed:                        1704
% 23.69/3.43  sim_bw_subsumed:                        42
% 23.69/3.43  sim_fw_subsumption_res:                 2
% 23.69/3.43  sim_bw_subsumption_res:                 1
% 23.69/3.43  sim_tautology_del:                      209
% 23.69/3.43  sim_eq_tautology_del:                   910
% 23.69/3.43  sim_eq_res_simp:                        0
% 23.69/3.43  sim_fw_demodulated:                     4043
% 23.69/3.43  sim_bw_demodulated:                     110
% 23.69/3.43  sim_light_normalised:                   2656
% 23.69/3.43  sim_joinable_taut:                      0
% 23.69/3.43  sim_joinable_simp:                      0
% 23.69/3.43  sim_ac_normalised:                      0
% 23.69/3.43  sim_smt_subsumption:                    0
% 23.69/3.43  
%------------------------------------------------------------------------------
