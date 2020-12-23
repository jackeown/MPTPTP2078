%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:44 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 340 expanded)
%              Number of clauses        :   51 ( 133 expanded)
%              Number of leaves         :   11 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  157 ( 751 expanded)
%              Number of equality atoms :   79 ( 199 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_509,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_517,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_908,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_509,c_517])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_508,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_514,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_985,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_508,c_514])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_516,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_520,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_512,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1633,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_520,c_512])).

cnf(c_2529,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_1633])).

cnf(c_10624,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_508,c_2529])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_511,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_899,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_511])).

cnf(c_3611,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_508,c_899])).

cnf(c_900,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_508,c_511])).

cnf(c_3612,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
    inference(demodulation,[status(thm)],[c_3611,c_900])).

cnf(c_11416,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_10624,c_3612])).

cnf(c_11417,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11416,c_900])).

cnf(c_11548,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_985,c_11417])).

cnf(c_11583,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k1_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_11548,c_985])).

cnf(c_11615,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_908,c_11583])).

cnf(c_11678,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_11615,c_908])).

cnf(c_984,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_516,c_514])).

cnf(c_4533,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_508,c_984])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_515,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_991,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_508,c_515])).

cnf(c_4534,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4533,c_991])).

cnf(c_4999,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4534,c_900])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_518,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_907,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_518,c_517])).

cnf(c_5023,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_4999,c_907])).

cnf(c_5064,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_5023,c_4999])).

cnf(c_11919,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_11678,c_5064])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_724,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_518])).

cnf(c_5024,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4999,c_724])).

cnf(c_11965,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11919,c_5024])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11965,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.73/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.01  
% 3.73/1.01  ------  iProver source info
% 3.73/1.01  
% 3.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.01  git: non_committed_changes: false
% 3.73/1.01  git: last_make_outside_of_git: false
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options
% 3.73/1.01  
% 3.73/1.01  --out_options                           all
% 3.73/1.01  --tptp_safe_out                         true
% 3.73/1.01  --problem_path                          ""
% 3.73/1.01  --include_path                          ""
% 3.73/1.01  --clausifier                            res/vclausify_rel
% 3.73/1.01  --clausifier_options                    ""
% 3.73/1.01  --stdin                                 false
% 3.73/1.01  --stats_out                             all
% 3.73/1.01  
% 3.73/1.01  ------ General Options
% 3.73/1.01  
% 3.73/1.01  --fof                                   false
% 3.73/1.01  --time_out_real                         305.
% 3.73/1.01  --time_out_virtual                      -1.
% 3.73/1.01  --symbol_type_check                     false
% 3.73/1.01  --clausify_out                          false
% 3.73/1.01  --sig_cnt_out                           false
% 3.73/1.01  --trig_cnt_out                          false
% 3.73/1.01  --trig_cnt_out_tolerance                1.
% 3.73/1.01  --trig_cnt_out_sk_spl                   false
% 3.73/1.01  --abstr_cl_out                          false
% 3.73/1.01  
% 3.73/1.01  ------ Global Options
% 3.73/1.01  
% 3.73/1.01  --schedule                              default
% 3.73/1.01  --add_important_lit                     false
% 3.73/1.01  --prop_solver_per_cl                    1000
% 3.73/1.01  --min_unsat_core                        false
% 3.73/1.01  --soft_assumptions                      false
% 3.73/1.01  --soft_lemma_size                       3
% 3.73/1.01  --prop_impl_unit_size                   0
% 3.73/1.01  --prop_impl_unit                        []
% 3.73/1.01  --share_sel_clauses                     true
% 3.73/1.01  --reset_solvers                         false
% 3.73/1.01  --bc_imp_inh                            [conj_cone]
% 3.73/1.01  --conj_cone_tolerance                   3.
% 3.73/1.01  --extra_neg_conj                        none
% 3.73/1.01  --large_theory_mode                     true
% 3.73/1.01  --prolific_symb_bound                   200
% 3.73/1.01  --lt_threshold                          2000
% 3.73/1.01  --clause_weak_htbl                      true
% 3.73/1.01  --gc_record_bc_elim                     false
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing Options
% 3.73/1.01  
% 3.73/1.01  --preprocessing_flag                    true
% 3.73/1.01  --time_out_prep_mult                    0.1
% 3.73/1.01  --splitting_mode                        input
% 3.73/1.01  --splitting_grd                         true
% 3.73/1.01  --splitting_cvd                         false
% 3.73/1.01  --splitting_cvd_svl                     false
% 3.73/1.01  --splitting_nvd                         32
% 3.73/1.01  --sub_typing                            true
% 3.73/1.01  --prep_gs_sim                           true
% 3.73/1.01  --prep_unflatten                        true
% 3.73/1.01  --prep_res_sim                          true
% 3.73/1.01  --prep_upred                            true
% 3.73/1.01  --prep_sem_filter                       exhaustive
% 3.73/1.01  --prep_sem_filter_out                   false
% 3.73/1.01  --pred_elim                             true
% 3.73/1.01  --res_sim_input                         true
% 3.73/1.01  --eq_ax_congr_red                       true
% 3.73/1.01  --pure_diseq_elim                       true
% 3.73/1.01  --brand_transform                       false
% 3.73/1.01  --non_eq_to_eq                          false
% 3.73/1.01  --prep_def_merge                        true
% 3.73/1.01  --prep_def_merge_prop_impl              false
% 3.73/1.01  --prep_def_merge_mbd                    true
% 3.73/1.01  --prep_def_merge_tr_red                 false
% 3.73/1.01  --prep_def_merge_tr_cl                  false
% 3.73/1.01  --smt_preprocessing                     true
% 3.73/1.01  --smt_ac_axioms                         fast
% 3.73/1.01  --preprocessed_out                      false
% 3.73/1.01  --preprocessed_stats                    false
% 3.73/1.01  
% 3.73/1.01  ------ Abstraction refinement Options
% 3.73/1.01  
% 3.73/1.01  --abstr_ref                             []
% 3.73/1.01  --abstr_ref_prep                        false
% 3.73/1.01  --abstr_ref_until_sat                   false
% 3.73/1.01  --abstr_ref_sig_restrict                funpre
% 3.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.01  --abstr_ref_under                       []
% 3.73/1.01  
% 3.73/1.01  ------ SAT Options
% 3.73/1.01  
% 3.73/1.01  --sat_mode                              false
% 3.73/1.01  --sat_fm_restart_options                ""
% 3.73/1.01  --sat_gr_def                            false
% 3.73/1.01  --sat_epr_types                         true
% 3.73/1.01  --sat_non_cyclic_types                  false
% 3.73/1.01  --sat_finite_models                     false
% 3.73/1.01  --sat_fm_lemmas                         false
% 3.73/1.01  --sat_fm_prep                           false
% 3.73/1.01  --sat_fm_uc_incr                        true
% 3.73/1.01  --sat_out_model                         small
% 3.73/1.01  --sat_out_clauses                       false
% 3.73/1.01  
% 3.73/1.01  ------ QBF Options
% 3.73/1.01  
% 3.73/1.01  --qbf_mode                              false
% 3.73/1.01  --qbf_elim_univ                         false
% 3.73/1.01  --qbf_dom_inst                          none
% 3.73/1.01  --qbf_dom_pre_inst                      false
% 3.73/1.01  --qbf_sk_in                             false
% 3.73/1.01  --qbf_pred_elim                         true
% 3.73/1.01  --qbf_split                             512
% 3.73/1.01  
% 3.73/1.01  ------ BMC1 Options
% 3.73/1.01  
% 3.73/1.01  --bmc1_incremental                      false
% 3.73/1.01  --bmc1_axioms                           reachable_all
% 3.73/1.01  --bmc1_min_bound                        0
% 3.73/1.01  --bmc1_max_bound                        -1
% 3.73/1.01  --bmc1_max_bound_default                -1
% 3.73/1.01  --bmc1_symbol_reachability              true
% 3.73/1.01  --bmc1_property_lemmas                  false
% 3.73/1.01  --bmc1_k_induction                      false
% 3.73/1.01  --bmc1_non_equiv_states                 false
% 3.73/1.01  --bmc1_deadlock                         false
% 3.73/1.01  --bmc1_ucm                              false
% 3.73/1.01  --bmc1_add_unsat_core                   none
% 3.73/1.01  --bmc1_unsat_core_children              false
% 3.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.01  --bmc1_out_stat                         full
% 3.73/1.01  --bmc1_ground_init                      false
% 3.73/1.01  --bmc1_pre_inst_next_state              false
% 3.73/1.01  --bmc1_pre_inst_state                   false
% 3.73/1.01  --bmc1_pre_inst_reach_state             false
% 3.73/1.01  --bmc1_out_unsat_core                   false
% 3.73/1.01  --bmc1_aig_witness_out                  false
% 3.73/1.01  --bmc1_verbose                          false
% 3.73/1.01  --bmc1_dump_clauses_tptp                false
% 3.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.01  --bmc1_dump_file                        -
% 3.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.01  --bmc1_ucm_extend_mode                  1
% 3.73/1.01  --bmc1_ucm_init_mode                    2
% 3.73/1.01  --bmc1_ucm_cone_mode                    none
% 3.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.01  --bmc1_ucm_relax_model                  4
% 3.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.01  --bmc1_ucm_layered_model                none
% 3.73/1.01  --bmc1_ucm_max_lemma_size               10
% 3.73/1.01  
% 3.73/1.01  ------ AIG Options
% 3.73/1.01  
% 3.73/1.01  --aig_mode                              false
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation Options
% 3.73/1.01  
% 3.73/1.01  --instantiation_flag                    true
% 3.73/1.01  --inst_sos_flag                         true
% 3.73/1.01  --inst_sos_phase                        true
% 3.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel_side                     num_symb
% 3.73/1.01  --inst_solver_per_active                1400
% 3.73/1.01  --inst_solver_calls_frac                1.
% 3.73/1.01  --inst_passive_queue_type               priority_queues
% 3.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.01  --inst_passive_queues_freq              [25;2]
% 3.73/1.01  --inst_dismatching                      true
% 3.73/1.01  --inst_eager_unprocessed_to_passive     true
% 3.73/1.01  --inst_prop_sim_given                   true
% 3.73/1.01  --inst_prop_sim_new                     false
% 3.73/1.01  --inst_subs_new                         false
% 3.73/1.01  --inst_eq_res_simp                      false
% 3.73/1.01  --inst_subs_given                       false
% 3.73/1.01  --inst_orphan_elimination               true
% 3.73/1.01  --inst_learning_loop_flag               true
% 3.73/1.01  --inst_learning_start                   3000
% 3.73/1.01  --inst_learning_factor                  2
% 3.73/1.01  --inst_start_prop_sim_after_learn       3
% 3.73/1.01  --inst_sel_renew                        solver
% 3.73/1.01  --inst_lit_activity_flag                true
% 3.73/1.01  --inst_restr_to_given                   false
% 3.73/1.01  --inst_activity_threshold               500
% 3.73/1.01  --inst_out_proof                        true
% 3.73/1.01  
% 3.73/1.01  ------ Resolution Options
% 3.73/1.01  
% 3.73/1.01  --resolution_flag                       true
% 3.73/1.01  --res_lit_sel                           adaptive
% 3.73/1.01  --res_lit_sel_side                      none
% 3.73/1.01  --res_ordering                          kbo
% 3.73/1.01  --res_to_prop_solver                    active
% 3.73/1.01  --res_prop_simpl_new                    false
% 3.73/1.01  --res_prop_simpl_given                  true
% 3.73/1.01  --res_passive_queue_type                priority_queues
% 3.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.01  --res_passive_queues_freq               [15;5]
% 3.73/1.01  --res_forward_subs                      full
% 3.73/1.01  --res_backward_subs                     full
% 3.73/1.01  --res_forward_subs_resolution           true
% 3.73/1.01  --res_backward_subs_resolution          true
% 3.73/1.01  --res_orphan_elimination                true
% 3.73/1.01  --res_time_limit                        2.
% 3.73/1.01  --res_out_proof                         true
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Options
% 3.73/1.01  
% 3.73/1.01  --superposition_flag                    true
% 3.73/1.01  --sup_passive_queue_type                priority_queues
% 3.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.01  --demod_completeness_check              fast
% 3.73/1.01  --demod_use_ground                      true
% 3.73/1.01  --sup_to_prop_solver                    passive
% 3.73/1.01  --sup_prop_simpl_new                    true
% 3.73/1.01  --sup_prop_simpl_given                  true
% 3.73/1.01  --sup_fun_splitting                     true
% 3.73/1.01  --sup_smt_interval                      50000
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Simplification Setup
% 3.73/1.01  
% 3.73/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.01  --sup_immed_triv                        [TrivRules]
% 3.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_bw_main                     []
% 3.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_input_bw                          []
% 3.73/1.01  
% 3.73/1.01  ------ Combination Options
% 3.73/1.01  
% 3.73/1.01  --comb_res_mult                         3
% 3.73/1.01  --comb_sup_mult                         2
% 3.73/1.01  --comb_inst_mult                        10
% 3.73/1.01  
% 3.73/1.01  ------ Debug Options
% 3.73/1.01  
% 3.73/1.01  --dbg_backtrace                         false
% 3.73/1.01  --dbg_dump_prop_clauses                 false
% 3.73/1.01  --dbg_dump_prop_clauses_file            -
% 3.73/1.01  --dbg_out_stat                          false
% 3.73/1.01  ------ Parsing...
% 3.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  ------ Proving...
% 3.73/1.01  ------ Problem Properties 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  clauses                                 15
% 3.73/1.01  conjectures                             3
% 3.73/1.01  EPR                                     3
% 3.73/1.01  Horn                                    15
% 3.73/1.01  unary                                   6
% 3.73/1.01  binary                                  6
% 3.73/1.01  lits                                    27
% 3.73/1.01  lits eq                                 7
% 3.73/1.01  fd_pure                                 0
% 3.73/1.01  fd_pseudo                               0
% 3.73/1.01  fd_cond                                 0
% 3.73/1.01  fd_pseudo_cond                          1
% 3.73/1.01  AC symbols                              0
% 3.73/1.01  
% 3.73/1.01  ------ Schedule dynamic 5 is on 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  Current options:
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  ------ Input Options
% 3.73/1.01  
% 3.73/1.01  --out_options                           all
% 3.73/1.01  --tptp_safe_out                         true
% 3.73/1.01  --problem_path                          ""
% 3.73/1.01  --include_path                          ""
% 3.73/1.01  --clausifier                            res/vclausify_rel
% 3.73/1.01  --clausifier_options                    ""
% 3.73/1.01  --stdin                                 false
% 3.73/1.01  --stats_out                             all
% 3.73/1.01  
% 3.73/1.01  ------ General Options
% 3.73/1.01  
% 3.73/1.01  --fof                                   false
% 3.73/1.01  --time_out_real                         305.
% 3.73/1.01  --time_out_virtual                      -1.
% 3.73/1.01  --symbol_type_check                     false
% 3.73/1.01  --clausify_out                          false
% 3.73/1.01  --sig_cnt_out                           false
% 3.73/1.01  --trig_cnt_out                          false
% 3.73/1.01  --trig_cnt_out_tolerance                1.
% 3.73/1.01  --trig_cnt_out_sk_spl                   false
% 3.73/1.01  --abstr_cl_out                          false
% 3.73/1.01  
% 3.73/1.01  ------ Global Options
% 3.73/1.01  
% 3.73/1.01  --schedule                              default
% 3.73/1.01  --add_important_lit                     false
% 3.73/1.01  --prop_solver_per_cl                    1000
% 3.73/1.01  --min_unsat_core                        false
% 3.73/1.01  --soft_assumptions                      false
% 3.73/1.01  --soft_lemma_size                       3
% 3.73/1.01  --prop_impl_unit_size                   0
% 3.73/1.01  --prop_impl_unit                        []
% 3.73/1.01  --share_sel_clauses                     true
% 3.73/1.01  --reset_solvers                         false
% 3.73/1.01  --bc_imp_inh                            [conj_cone]
% 3.73/1.01  --conj_cone_tolerance                   3.
% 3.73/1.01  --extra_neg_conj                        none
% 3.73/1.01  --large_theory_mode                     true
% 3.73/1.01  --prolific_symb_bound                   200
% 3.73/1.01  --lt_threshold                          2000
% 3.73/1.01  --clause_weak_htbl                      true
% 3.73/1.01  --gc_record_bc_elim                     false
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing Options
% 3.73/1.01  
% 3.73/1.01  --preprocessing_flag                    true
% 3.73/1.01  --time_out_prep_mult                    0.1
% 3.73/1.01  --splitting_mode                        input
% 3.73/1.01  --splitting_grd                         true
% 3.73/1.01  --splitting_cvd                         false
% 3.73/1.01  --splitting_cvd_svl                     false
% 3.73/1.01  --splitting_nvd                         32
% 3.73/1.01  --sub_typing                            true
% 3.73/1.01  --prep_gs_sim                           true
% 3.73/1.01  --prep_unflatten                        true
% 3.73/1.01  --prep_res_sim                          true
% 3.73/1.01  --prep_upred                            true
% 3.73/1.01  --prep_sem_filter                       exhaustive
% 3.73/1.01  --prep_sem_filter_out                   false
% 3.73/1.01  --pred_elim                             true
% 3.73/1.01  --res_sim_input                         true
% 3.73/1.01  --eq_ax_congr_red                       true
% 3.73/1.01  --pure_diseq_elim                       true
% 3.73/1.01  --brand_transform                       false
% 3.73/1.01  --non_eq_to_eq                          false
% 3.73/1.01  --prep_def_merge                        true
% 3.73/1.01  --prep_def_merge_prop_impl              false
% 3.73/1.01  --prep_def_merge_mbd                    true
% 3.73/1.01  --prep_def_merge_tr_red                 false
% 3.73/1.01  --prep_def_merge_tr_cl                  false
% 3.73/1.01  --smt_preprocessing                     true
% 3.73/1.01  --smt_ac_axioms                         fast
% 3.73/1.01  --preprocessed_out                      false
% 3.73/1.01  --preprocessed_stats                    false
% 3.73/1.01  
% 3.73/1.01  ------ Abstraction refinement Options
% 3.73/1.01  
% 3.73/1.01  --abstr_ref                             []
% 3.73/1.01  --abstr_ref_prep                        false
% 3.73/1.01  --abstr_ref_until_sat                   false
% 3.73/1.01  --abstr_ref_sig_restrict                funpre
% 3.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.01  --abstr_ref_under                       []
% 3.73/1.01  
% 3.73/1.01  ------ SAT Options
% 3.73/1.01  
% 3.73/1.01  --sat_mode                              false
% 3.73/1.01  --sat_fm_restart_options                ""
% 3.73/1.01  --sat_gr_def                            false
% 3.73/1.01  --sat_epr_types                         true
% 3.73/1.01  --sat_non_cyclic_types                  false
% 3.73/1.01  --sat_finite_models                     false
% 3.73/1.01  --sat_fm_lemmas                         false
% 3.73/1.01  --sat_fm_prep                           false
% 3.73/1.01  --sat_fm_uc_incr                        true
% 3.73/1.01  --sat_out_model                         small
% 3.73/1.01  --sat_out_clauses                       false
% 3.73/1.01  
% 3.73/1.01  ------ QBF Options
% 3.73/1.01  
% 3.73/1.01  --qbf_mode                              false
% 3.73/1.01  --qbf_elim_univ                         false
% 3.73/1.01  --qbf_dom_inst                          none
% 3.73/1.01  --qbf_dom_pre_inst                      false
% 3.73/1.01  --qbf_sk_in                             false
% 3.73/1.01  --qbf_pred_elim                         true
% 3.73/1.01  --qbf_split                             512
% 3.73/1.01  
% 3.73/1.01  ------ BMC1 Options
% 3.73/1.01  
% 3.73/1.01  --bmc1_incremental                      false
% 3.73/1.01  --bmc1_axioms                           reachable_all
% 3.73/1.01  --bmc1_min_bound                        0
% 3.73/1.01  --bmc1_max_bound                        -1
% 3.73/1.01  --bmc1_max_bound_default                -1
% 3.73/1.01  --bmc1_symbol_reachability              true
% 3.73/1.01  --bmc1_property_lemmas                  false
% 3.73/1.01  --bmc1_k_induction                      false
% 3.73/1.01  --bmc1_non_equiv_states                 false
% 3.73/1.01  --bmc1_deadlock                         false
% 3.73/1.01  --bmc1_ucm                              false
% 3.73/1.01  --bmc1_add_unsat_core                   none
% 3.73/1.01  --bmc1_unsat_core_children              false
% 3.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.01  --bmc1_out_stat                         full
% 3.73/1.01  --bmc1_ground_init                      false
% 3.73/1.01  --bmc1_pre_inst_next_state              false
% 3.73/1.01  --bmc1_pre_inst_state                   false
% 3.73/1.01  --bmc1_pre_inst_reach_state             false
% 3.73/1.01  --bmc1_out_unsat_core                   false
% 3.73/1.01  --bmc1_aig_witness_out                  false
% 3.73/1.01  --bmc1_verbose                          false
% 3.73/1.01  --bmc1_dump_clauses_tptp                false
% 3.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.01  --bmc1_dump_file                        -
% 3.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.01  --bmc1_ucm_extend_mode                  1
% 3.73/1.01  --bmc1_ucm_init_mode                    2
% 3.73/1.01  --bmc1_ucm_cone_mode                    none
% 3.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.01  --bmc1_ucm_relax_model                  4
% 3.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.01  --bmc1_ucm_layered_model                none
% 3.73/1.01  --bmc1_ucm_max_lemma_size               10
% 3.73/1.01  
% 3.73/1.01  ------ AIG Options
% 3.73/1.01  
% 3.73/1.01  --aig_mode                              false
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation Options
% 3.73/1.01  
% 3.73/1.01  --instantiation_flag                    true
% 3.73/1.01  --inst_sos_flag                         true
% 3.73/1.01  --inst_sos_phase                        true
% 3.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.01  --inst_lit_sel_side                     none
% 3.73/1.01  --inst_solver_per_active                1400
% 3.73/1.01  --inst_solver_calls_frac                1.
% 3.73/1.01  --inst_passive_queue_type               priority_queues
% 3.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.01  --inst_passive_queues_freq              [25;2]
% 3.73/1.01  --inst_dismatching                      true
% 3.73/1.01  --inst_eager_unprocessed_to_passive     true
% 3.73/1.01  --inst_prop_sim_given                   true
% 3.73/1.01  --inst_prop_sim_new                     false
% 3.73/1.01  --inst_subs_new                         false
% 3.73/1.01  --inst_eq_res_simp                      false
% 3.73/1.01  --inst_subs_given                       false
% 3.73/1.01  --inst_orphan_elimination               true
% 3.73/1.01  --inst_learning_loop_flag               true
% 3.73/1.01  --inst_learning_start                   3000
% 3.73/1.01  --inst_learning_factor                  2
% 3.73/1.01  --inst_start_prop_sim_after_learn       3
% 3.73/1.01  --inst_sel_renew                        solver
% 3.73/1.01  --inst_lit_activity_flag                true
% 3.73/1.01  --inst_restr_to_given                   false
% 3.73/1.01  --inst_activity_threshold               500
% 3.73/1.01  --inst_out_proof                        true
% 3.73/1.01  
% 3.73/1.01  ------ Resolution Options
% 3.73/1.01  
% 3.73/1.01  --resolution_flag                       false
% 3.73/1.01  --res_lit_sel                           adaptive
% 3.73/1.01  --res_lit_sel_side                      none
% 3.73/1.01  --res_ordering                          kbo
% 3.73/1.01  --res_to_prop_solver                    active
% 3.73/1.01  --res_prop_simpl_new                    false
% 3.73/1.01  --res_prop_simpl_given                  true
% 3.73/1.01  --res_passive_queue_type                priority_queues
% 3.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.01  --res_passive_queues_freq               [15;5]
% 3.73/1.01  --res_forward_subs                      full
% 3.73/1.01  --res_backward_subs                     full
% 3.73/1.01  --res_forward_subs_resolution           true
% 3.73/1.01  --res_backward_subs_resolution          true
% 3.73/1.01  --res_orphan_elimination                true
% 3.73/1.01  --res_time_limit                        2.
% 3.73/1.01  --res_out_proof                         true
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Options
% 3.73/1.01  
% 3.73/1.01  --superposition_flag                    true
% 3.73/1.01  --sup_passive_queue_type                priority_queues
% 3.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.01  --demod_completeness_check              fast
% 3.73/1.01  --demod_use_ground                      true
% 3.73/1.01  --sup_to_prop_solver                    passive
% 3.73/1.01  --sup_prop_simpl_new                    true
% 3.73/1.01  --sup_prop_simpl_given                  true
% 3.73/1.01  --sup_fun_splitting                     true
% 3.73/1.01  --sup_smt_interval                      50000
% 3.73/1.01  
% 3.73/1.01  ------ Superposition Simplification Setup
% 3.73/1.01  
% 3.73/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.01  --sup_immed_triv                        [TrivRules]
% 3.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_immed_bw_main                     []
% 3.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.01  --sup_input_bw                          []
% 3.73/1.01  
% 3.73/1.01  ------ Combination Options
% 3.73/1.01  
% 3.73/1.01  --comb_res_mult                         3
% 3.73/1.01  --comb_sup_mult                         2
% 3.73/1.01  --comb_inst_mult                        10
% 3.73/1.01  
% 3.73/1.01  ------ Debug Options
% 3.73/1.01  
% 3.73/1.01  --dbg_backtrace                         false
% 3.73/1.01  --dbg_dump_prop_clauses                 false
% 3.73/1.01  --dbg_dump_prop_clauses_file            -
% 3.73/1.01  --dbg_out_stat                          false
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS status Theorem for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  fof(f12,conjecture,(
% 3.73/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f13,negated_conjecture,(
% 3.73/1.01    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.73/1.01    inference(negated_conjecture,[],[f12])).
% 3.73/1.01  
% 3.73/1.01  fof(f24,plain,(
% 3.73/1.01    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f13])).
% 3.73/1.01  
% 3.73/1.01  fof(f25,plain,(
% 3.73/1.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.73/1.01    inference(flattening,[],[f24])).
% 3.73/1.01  
% 3.73/1.01  fof(f28,plain,(
% 3.73/1.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f29,plain,(
% 3.73/1.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).
% 3.73/1.01  
% 3.73/1.01  fof(f44,plain,(
% 3.73/1.01    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f5,axiom,(
% 3.73/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f15,plain,(
% 3.73/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f5])).
% 3.73/1.01  
% 3.73/1.01  fof(f36,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f15])).
% 3.73/1.01  
% 3.73/1.01  fof(f43,plain,(
% 3.73/1.01    v1_relat_1(sK1)),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f8,axiom,(
% 3.73/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f18,plain,(
% 3.73/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f8])).
% 3.73/1.01  
% 3.73/1.01  fof(f39,plain,(
% 3.73/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f18])).
% 3.73/1.01  
% 3.73/1.01  fof(f6,axiom,(
% 3.73/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f16,plain,(
% 3.73/1.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f6])).
% 3.73/1.01  
% 3.73/1.01  fof(f37,plain,(
% 3.73/1.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f16])).
% 3.73/1.01  
% 3.73/1.01  fof(f2,axiom,(
% 3.73/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f26,plain,(
% 3.73/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.01    inference(nnf_transformation,[],[f2])).
% 3.73/1.01  
% 3.73/1.01  fof(f27,plain,(
% 3.73/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.01    inference(flattening,[],[f26])).
% 3.73/1.01  
% 3.73/1.01  fof(f31,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.73/1.01    inference(cnf_transformation,[],[f27])).
% 3.73/1.01  
% 3.73/1.01  fof(f47,plain,(
% 3.73/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.01    inference(equality_resolution,[],[f31])).
% 3.73/1.01  
% 3.73/1.01  fof(f10,axiom,(
% 3.73/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f21,plain,(
% 3.73/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f10])).
% 3.73/1.01  
% 3.73/1.01  fof(f22,plain,(
% 3.73/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.73/1.01    inference(flattening,[],[f21])).
% 3.73/1.01  
% 3.73/1.01  fof(f41,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f22])).
% 3.73/1.01  
% 3.73/1.01  fof(f11,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f23,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.73/1.01    inference(ennf_transformation,[],[f11])).
% 3.73/1.01  
% 3.73/1.01  fof(f42,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f23])).
% 3.73/1.01  
% 3.73/1.01  fof(f7,axiom,(
% 3.73/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f17,plain,(
% 3.73/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f7])).
% 3.73/1.01  
% 3.73/1.01  fof(f38,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f17])).
% 3.73/1.01  
% 3.73/1.01  fof(f4,axiom,(
% 3.73/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f35,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f4])).
% 3.73/1.01  
% 3.73/1.01  fof(f1,axiom,(
% 3.73/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f30,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f1])).
% 3.73/1.01  
% 3.73/1.01  fof(f45,plain,(
% 3.73/1.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  cnf(c_14,negated_conjecture,
% 3.73/1.01      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_509,plain,
% 3.73/1.01      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_6,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_517,plain,
% 3.73/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_908,plain,
% 3.73/1.01      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_509,c_517]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_15,negated_conjecture,
% 3.73/1.01      ( v1_relat_1(sK1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_508,plain,
% 3.73/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_9,plain,
% 3.73/1.01      ( ~ v1_relat_1(X0)
% 3.73/1.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_514,plain,
% 3.73/1.01      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_985,plain,
% 3.73/1.01      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_514]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_7,plain,
% 3.73/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_516,plain,
% 3.73/1.01      ( v1_relat_1(X0) != iProver_top
% 3.73/1.01      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3,plain,
% 3.73/1.01      ( r1_tarski(X0,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_520,plain,
% 3.73/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11,plain,
% 3.73/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.73/1.01      | ~ v1_relat_1(X0)
% 3.73/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_512,plain,
% 3.73/1.01      ( k7_relat_1(X0,X1) = X0
% 3.73/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1633,plain,
% 3.73/1.01      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_520,c_512]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2529,plain,
% 3.73/1.01      ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_516,c_1633]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_10624,plain,
% 3.73/1.01      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_2529]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_12,plain,
% 3.73/1.01      ( ~ v1_relat_1(X0)
% 3.73/1.01      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_511,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_899,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_516,c_511]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3611,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_899]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_900,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_511]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3612,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_3611,c_900]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11416,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_10624,c_3612]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11417,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 3.73/1.01      inference(light_normalisation,[status(thm)],[c_11416,c_900]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11548,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_985,c_11417]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11583,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k1_relat_1(sK1)) ),
% 3.73/1.01      inference(light_normalisation,[status(thm)],[c_11548,c_985]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11615,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_908,c_11583]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11678,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = sK0 ),
% 3.73/1.01      inference(light_normalisation,[status(thm)],[c_11615,c_908]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_984,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_516,c_514]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4533,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_984]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8,plain,
% 3.73/1.01      ( ~ v1_relat_1(X0)
% 3.73/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_515,plain,
% 3.73/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.73/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_991,plain,
% 3.73/1.01      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_508,c_515]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4534,plain,
% 3.73/1.01      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.73/1.01      inference(light_normalisation,[status(thm)],[c_4533,c_991]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4999,plain,
% 3.73/1.01      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_4534,c_900]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5,plain,
% 3.73/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_518,plain,
% 3.73/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_907,plain,
% 3.73/1.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_518,c_517]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5023,plain,
% 3.73/1.01      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_4999,c_907]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5064,plain,
% 3.73/1.01      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_5023,c_4999]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11919,plain,
% 3.73/1.01      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_11678,c_5064]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_0,plain,
% 3.73/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_724,plain,
% 3.73/1.01      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_0,c_518]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5024,plain,
% 3.73/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_4999,c_724]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11965,plain,
% 3.73/1.01      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_11919,c_5024]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13,negated_conjecture,
% 3.73/1.01      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 3.73/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_18,plain,
% 3.73/1.01      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(contradiction,plain,
% 3.73/1.01      ( $false ),
% 3.73/1.01      inference(minisat,[status(thm)],[c_11965,c_18]) ).
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  ------                               Statistics
% 3.73/1.01  
% 3.73/1.01  ------ General
% 3.73/1.01  
% 3.73/1.01  abstr_ref_over_cycles:                  0
% 3.73/1.01  abstr_ref_under_cycles:                 0
% 3.73/1.01  gc_basic_clause_elim:                   0
% 3.73/1.01  forced_gc_time:                         0
% 3.73/1.01  parsing_time:                           0.01
% 3.73/1.01  unif_index_cands_time:                  0.
% 3.73/1.01  unif_index_add_time:                    0.
% 3.73/1.01  orderings_time:                         0.
% 3.73/1.01  out_proof_time:                         0.007
% 3.73/1.01  total_time:                             0.358
% 3.73/1.01  num_of_symbols:                         41
% 3.73/1.01  num_of_terms:                           10843
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing
% 3.73/1.01  
% 3.73/1.01  num_of_splits:                          0
% 3.73/1.01  num_of_split_atoms:                     0
% 3.73/1.01  num_of_reused_defs:                     0
% 3.73/1.01  num_eq_ax_congr_red:                    9
% 3.73/1.01  num_of_sem_filtered_clauses:            1
% 3.73/1.01  num_of_subtypes:                        0
% 3.73/1.01  monotx_restored_types:                  0
% 3.73/1.01  sat_num_of_epr_types:                   0
% 3.73/1.01  sat_num_of_non_cyclic_types:            0
% 3.73/1.01  sat_guarded_non_collapsed_types:        0
% 3.73/1.01  num_pure_diseq_elim:                    0
% 3.73/1.01  simp_replaced_by:                       0
% 3.73/1.01  res_preprocessed:                       79
% 3.73/1.01  prep_upred:                             0
% 3.73/1.01  prep_unflattend:                        0
% 3.73/1.01  smt_new_axioms:                         0
% 3.73/1.01  pred_elim_cands:                        2
% 3.73/1.01  pred_elim:                              0
% 3.73/1.01  pred_elim_cl:                           0
% 3.73/1.01  pred_elim_cycles:                       2
% 3.73/1.01  merged_defs:                            0
% 3.73/1.01  merged_defs_ncl:                        0
% 3.73/1.01  bin_hyper_res:                          0
% 3.73/1.01  prep_cycles:                            4
% 3.73/1.01  pred_elim_time:                         0.
% 3.73/1.01  splitting_time:                         0.
% 3.73/1.01  sem_filter_time:                        0.
% 3.73/1.01  monotx_time:                            0.
% 3.73/1.01  subtype_inf_time:                       0.
% 3.73/1.01  
% 3.73/1.01  ------ Problem properties
% 3.73/1.01  
% 3.73/1.01  clauses:                                15
% 3.73/1.01  conjectures:                            3
% 3.73/1.01  epr:                                    3
% 3.73/1.01  horn:                                   15
% 3.73/1.01  ground:                                 3
% 3.73/1.01  unary:                                  6
% 3.73/1.01  binary:                                 6
% 3.73/1.01  lits:                                   27
% 3.73/1.01  lits_eq:                                7
% 3.73/1.01  fd_pure:                                0
% 3.73/1.01  fd_pseudo:                              0
% 3.73/1.01  fd_cond:                                0
% 3.73/1.01  fd_pseudo_cond:                         1
% 3.73/1.01  ac_symbols:                             0
% 3.73/1.01  
% 3.73/1.01  ------ Propositional Solver
% 3.73/1.01  
% 3.73/1.01  prop_solver_calls:                      33
% 3.73/1.01  prop_fast_solver_calls:                 529
% 3.73/1.01  smt_solver_calls:                       0
% 3.73/1.01  smt_fast_solver_calls:                  0
% 3.73/1.01  prop_num_of_clauses:                    4988
% 3.73/1.01  prop_preprocess_simplified:             8258
% 3.73/1.01  prop_fo_subsumed:                       4
% 3.73/1.01  prop_solver_time:                       0.
% 3.73/1.01  smt_solver_time:                        0.
% 3.73/1.01  smt_fast_solver_time:                   0.
% 3.73/1.01  prop_fast_solver_time:                  0.
% 3.73/1.01  prop_unsat_core_time:                   0.
% 3.73/1.01  
% 3.73/1.01  ------ QBF
% 3.73/1.01  
% 3.73/1.01  qbf_q_res:                              0
% 3.73/1.01  qbf_num_tautologies:                    0
% 3.73/1.01  qbf_prep_cycles:                        0
% 3.73/1.01  
% 3.73/1.01  ------ BMC1
% 3.73/1.01  
% 3.73/1.01  bmc1_current_bound:                     -1
% 3.73/1.01  bmc1_last_solved_bound:                 -1
% 3.73/1.01  bmc1_unsat_core_size:                   -1
% 3.73/1.01  bmc1_unsat_core_parents_size:           -1
% 3.73/1.01  bmc1_merge_next_fun:                    0
% 3.73/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.01  
% 3.73/1.01  ------ Instantiation
% 3.73/1.01  
% 3.73/1.01  inst_num_of_clauses:                    1345
% 3.73/1.01  inst_num_in_passive:                    298
% 3.73/1.01  inst_num_in_active:                     568
% 3.73/1.01  inst_num_in_unprocessed:                481
% 3.73/1.01  inst_num_of_loops:                      610
% 3.73/1.01  inst_num_of_learning_restarts:          0
% 3.73/1.01  inst_num_moves_active_passive:          30
% 3.73/1.01  inst_lit_activity:                      0
% 3.73/1.01  inst_lit_activity_moves:                0
% 3.73/1.01  inst_num_tautologies:                   0
% 3.73/1.01  inst_num_prop_implied:                  0
% 3.73/1.01  inst_num_existing_simplified:           0
% 3.73/1.01  inst_num_eq_res_simplified:             0
% 3.73/1.01  inst_num_child_elim:                    0
% 3.73/1.01  inst_num_of_dismatching_blockings:      882
% 3.73/1.01  inst_num_of_non_proper_insts:           1816
% 3.73/1.01  inst_num_of_duplicates:                 0
% 3.73/1.01  inst_inst_num_from_inst_to_res:         0
% 3.73/1.01  inst_dismatching_checking_time:         0.
% 3.73/1.01  
% 3.73/1.01  ------ Resolution
% 3.73/1.01  
% 3.73/1.01  res_num_of_clauses:                     0
% 3.73/1.01  res_num_in_passive:                     0
% 3.73/1.01  res_num_in_active:                      0
% 3.73/1.01  res_num_of_loops:                       83
% 3.73/1.01  res_forward_subset_subsumed:            325
% 3.73/1.01  res_backward_subset_subsumed:           20
% 3.73/1.01  res_forward_subsumed:                   0
% 3.73/1.01  res_backward_subsumed:                  0
% 3.73/1.01  res_forward_subsumption_resolution:     0
% 3.73/1.01  res_backward_subsumption_resolution:    0
% 3.73/1.01  res_clause_to_clause_subsumption:       6106
% 3.73/1.01  res_orphan_elimination:                 0
% 3.73/1.01  res_tautology_del:                      179
% 3.73/1.01  res_num_eq_res_simplified:              0
% 3.73/1.01  res_num_sel_changes:                    0
% 3.73/1.01  res_moves_from_active_to_pass:          0
% 3.73/1.01  
% 3.73/1.01  ------ Superposition
% 3.73/1.01  
% 3.73/1.01  sup_time_total:                         0.
% 3.73/1.01  sup_time_generating:                    0.
% 3.73/1.01  sup_time_sim_full:                      0.
% 3.73/1.01  sup_time_sim_immed:                     0.
% 3.73/1.01  
% 3.73/1.01  sup_num_of_clauses:                     417
% 3.73/1.01  sup_num_in_active:                      117
% 3.73/1.01  sup_num_in_passive:                     300
% 3.73/1.01  sup_num_of_loops:                       121
% 3.73/1.01  sup_fw_superposition:                   1132
% 3.73/1.01  sup_bw_superposition:                   915
% 3.73/1.01  sup_immediate_simplified:               857
% 3.73/1.01  sup_given_eliminated:                   1
% 3.73/1.01  comparisons_done:                       0
% 3.73/1.01  comparisons_avoided:                    0
% 3.73/1.01  
% 3.73/1.01  ------ Simplifications
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  sim_fw_subset_subsumed:                 43
% 3.73/1.01  sim_bw_subset_subsumed:                 3
% 3.73/1.01  sim_fw_subsumed:                        218
% 3.73/1.01  sim_bw_subsumed:                        1
% 3.73/1.01  sim_fw_subsumption_res:                 0
% 3.73/1.01  sim_bw_subsumption_res:                 0
% 3.73/1.01  sim_tautology_del:                      60
% 3.73/1.01  sim_eq_tautology_del:                   67
% 3.73/1.01  sim_eq_res_simp:                        0
% 3.73/1.01  sim_fw_demodulated:                     409
% 3.73/1.01  sim_bw_demodulated:                     5
% 3.73/1.01  sim_light_normalised:                   288
% 3.73/1.01  sim_joinable_taut:                      0
% 3.73/1.01  sim_joinable_simp:                      0
% 3.73/1.01  sim_ac_normalised:                      0
% 3.73/1.01  sim_smt_subsumption:                    0
% 3.73/1.01  
%------------------------------------------------------------------------------
