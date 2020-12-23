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
% DateTime   : Thu Dec  3 11:51:45 EST 2020

% Result     : Theorem 19.43s
% Output     : CNFRefutation 19.43s
% Verified   : 
% Statistics : Number of formulae       :  149 (1208 expanded)
%              Number of clauses        :  102 ( 524 expanded)
%              Number of leaves         :   14 ( 223 expanded)
%              Depth                    :   31
%              Number of atoms          :  247 (2412 expanded)
%              Number of equality atoms :  142 ( 843 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_544,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_549,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1159,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_544,c_549])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_551,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_557,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_548,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1677,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_548])).

cnf(c_7131,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_1677])).

cnf(c_87245,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_544,c_7131])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_547,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1061,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_547])).

cnf(c_2684,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_544,c_1061])).

cnf(c_1062,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_544,c_547])).

cnf(c_2685,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
    inference(demodulation,[status(thm)],[c_2684,c_1062])).

cnf(c_90312,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_87245,c_2685])).

cnf(c_90313,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_90312,c_1062])).

cnf(c_90977,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_1159,c_90313])).

cnf(c_91064,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k1_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_90977,c_1159])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1158,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_549])).

cnf(c_3928,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_544,c_1158])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_550,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1270,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_544,c_550])).

cnf(c_3929,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3928,c_1270])).

cnf(c_4548,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1062,c_3929])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_554,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_553,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1069,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_554,c_553])).

cnf(c_2810,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1069])).

cnf(c_2843,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2810,c_0])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_545,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_555,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1152,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_554,c_555])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_556,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1823,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_556])).

cnf(c_9290,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_555])).

cnf(c_25810,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_545,c_9290])).

cnf(c_878,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_554])).

cnf(c_1154,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_878,c_555])).

cnf(c_1820,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_556])).

cnf(c_2150,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_556])).

cnf(c_6097,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_2150])).

cnf(c_43725,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25810,c_6097])).

cnf(c_44373,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_43725,c_553])).

cnf(c_48021,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
    inference(superposition,[status(thm)],[c_2843,c_44373])).

cnf(c_48123,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
    inference(demodulation,[status(thm)],[c_48021,c_44373])).

cnf(c_1071,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_878,c_553])).

cnf(c_4168,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1071,c_0])).

cnf(c_48124,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK0)) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
    inference(demodulation,[status(thm)],[c_48123,c_4168])).

cnf(c_53229,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(X1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_0,c_48124])).

cnf(c_25809,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0) = X0 ),
    inference(superposition,[status(thm)],[c_554,c_9290])).

cnf(c_55096,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_53229,c_25809])).

cnf(c_59285,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_55096])).

cnf(c_59468,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_59285,c_1820])).

cnf(c_63610,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2810,c_59468])).

cnf(c_64133,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_63610])).

cnf(c_64216,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_64133])).

cnf(c_1962,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_556])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_552,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1948,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,X1)
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_552,c_553])).

cnf(c_20480,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,X0),k1_relat_1(sK1)) = k2_xboole_0(sK0,X0)
    | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1948])).

cnf(c_21547,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,X1)),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,X1))
    | r1_tarski(X1,k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_20480])).

cnf(c_65206,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))))),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))))) ),
    inference(superposition,[status(thm)],[c_64216,c_21547])).

cnf(c_1070,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_545,c_553])).

cnf(c_65209,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(light_normalisation,[status(thm)],[c_65206,c_1070])).

cnf(c_65661,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(superposition,[status(thm)],[c_0,c_65209])).

cnf(c_91210,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0)))) = k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_91064,c_65661])).

cnf(c_91240,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))) = k3_xboole_0(k2_xboole_0(sK0,sK0),k1_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_91210,c_1070])).

cnf(c_1151,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_557,c_555])).

cnf(c_2821,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1069,c_0])).

cnf(c_4553,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_4548,c_2821])).

cnf(c_4566,plain,
    ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_4553,c_4548])).

cnf(c_91241,plain,
    ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0 ),
    inference(demodulation,[status(thm)],[c_91240,c_1070,c_1151,c_4566])).

cnf(c_4557,plain,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_4548,c_1152])).

cnf(c_6104,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_2150,c_553])).

cnf(c_6380,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k2_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4557,c_6104])).

cnf(c_91797,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_91241,c_6380])).

cnf(c_54915,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),X1) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_53229,c_0])).

cnf(c_57030,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),X0) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_54915,c_1071])).

cnf(c_91167,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k3_xboole_0(sK0,k1_relat_1(sK1))) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_57030,c_91064])).

cnf(c_2833,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_1070,c_2810])).

cnf(c_2849,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2833,c_1070])).

cnf(c_91267,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_91167,c_1070,c_2849])).

cnf(c_91836,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_91797,c_91267])).

cnf(c_4558,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_878])).

cnf(c_91919,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_91836,c_4558])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91919,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:26:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.43/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.43/2.98  
% 19.43/2.98  ------  iProver source info
% 19.43/2.98  
% 19.43/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.43/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.43/2.98  git: non_committed_changes: false
% 19.43/2.98  git: last_make_outside_of_git: false
% 19.43/2.98  
% 19.43/2.98  ------ 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options
% 19.43/2.98  
% 19.43/2.98  --out_options                           all
% 19.43/2.98  --tptp_safe_out                         true
% 19.43/2.98  --problem_path                          ""
% 19.43/2.98  --include_path                          ""
% 19.43/2.98  --clausifier                            res/vclausify_rel
% 19.43/2.98  --clausifier_options                    ""
% 19.43/2.98  --stdin                                 false
% 19.43/2.98  --stats_out                             all
% 19.43/2.98  
% 19.43/2.98  ------ General Options
% 19.43/2.98  
% 19.43/2.98  --fof                                   false
% 19.43/2.98  --time_out_real                         305.
% 19.43/2.98  --time_out_virtual                      -1.
% 19.43/2.98  --symbol_type_check                     false
% 19.43/2.98  --clausify_out                          false
% 19.43/2.98  --sig_cnt_out                           false
% 19.43/2.98  --trig_cnt_out                          false
% 19.43/2.98  --trig_cnt_out_tolerance                1.
% 19.43/2.98  --trig_cnt_out_sk_spl                   false
% 19.43/2.98  --abstr_cl_out                          false
% 19.43/2.98  
% 19.43/2.98  ------ Global Options
% 19.43/2.98  
% 19.43/2.98  --schedule                              default
% 19.43/2.98  --add_important_lit                     false
% 19.43/2.98  --prop_solver_per_cl                    1000
% 19.43/2.98  --min_unsat_core                        false
% 19.43/2.98  --soft_assumptions                      false
% 19.43/2.98  --soft_lemma_size                       3
% 19.43/2.98  --prop_impl_unit_size                   0
% 19.43/2.98  --prop_impl_unit                        []
% 19.43/2.98  --share_sel_clauses                     true
% 19.43/2.98  --reset_solvers                         false
% 19.43/2.98  --bc_imp_inh                            [conj_cone]
% 19.43/2.98  --conj_cone_tolerance                   3.
% 19.43/2.98  --extra_neg_conj                        none
% 19.43/2.98  --large_theory_mode                     true
% 19.43/2.98  --prolific_symb_bound                   200
% 19.43/2.98  --lt_threshold                          2000
% 19.43/2.98  --clause_weak_htbl                      true
% 19.43/2.98  --gc_record_bc_elim                     false
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing Options
% 19.43/2.98  
% 19.43/2.98  --preprocessing_flag                    true
% 19.43/2.98  --time_out_prep_mult                    0.1
% 19.43/2.98  --splitting_mode                        input
% 19.43/2.98  --splitting_grd                         true
% 19.43/2.98  --splitting_cvd                         false
% 19.43/2.98  --splitting_cvd_svl                     false
% 19.43/2.98  --splitting_nvd                         32
% 19.43/2.98  --sub_typing                            true
% 19.43/2.98  --prep_gs_sim                           true
% 19.43/2.98  --prep_unflatten                        true
% 19.43/2.98  --prep_res_sim                          true
% 19.43/2.98  --prep_upred                            true
% 19.43/2.98  --prep_sem_filter                       exhaustive
% 19.43/2.98  --prep_sem_filter_out                   false
% 19.43/2.98  --pred_elim                             true
% 19.43/2.98  --res_sim_input                         true
% 19.43/2.98  --eq_ax_congr_red                       true
% 19.43/2.98  --pure_diseq_elim                       true
% 19.43/2.98  --brand_transform                       false
% 19.43/2.98  --non_eq_to_eq                          false
% 19.43/2.98  --prep_def_merge                        true
% 19.43/2.98  --prep_def_merge_prop_impl              false
% 19.43/2.98  --prep_def_merge_mbd                    true
% 19.43/2.98  --prep_def_merge_tr_red                 false
% 19.43/2.98  --prep_def_merge_tr_cl                  false
% 19.43/2.98  --smt_preprocessing                     true
% 19.43/2.98  --smt_ac_axioms                         fast
% 19.43/2.98  --preprocessed_out                      false
% 19.43/2.98  --preprocessed_stats                    false
% 19.43/2.98  
% 19.43/2.98  ------ Abstraction refinement Options
% 19.43/2.98  
% 19.43/2.98  --abstr_ref                             []
% 19.43/2.98  --abstr_ref_prep                        false
% 19.43/2.98  --abstr_ref_until_sat                   false
% 19.43/2.98  --abstr_ref_sig_restrict                funpre
% 19.43/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/2.98  --abstr_ref_under                       []
% 19.43/2.98  
% 19.43/2.98  ------ SAT Options
% 19.43/2.98  
% 19.43/2.98  --sat_mode                              false
% 19.43/2.98  --sat_fm_restart_options                ""
% 19.43/2.98  --sat_gr_def                            false
% 19.43/2.98  --sat_epr_types                         true
% 19.43/2.98  --sat_non_cyclic_types                  false
% 19.43/2.98  --sat_finite_models                     false
% 19.43/2.98  --sat_fm_lemmas                         false
% 19.43/2.98  --sat_fm_prep                           false
% 19.43/2.98  --sat_fm_uc_incr                        true
% 19.43/2.98  --sat_out_model                         small
% 19.43/2.98  --sat_out_clauses                       false
% 19.43/2.98  
% 19.43/2.98  ------ QBF Options
% 19.43/2.98  
% 19.43/2.98  --qbf_mode                              false
% 19.43/2.98  --qbf_elim_univ                         false
% 19.43/2.98  --qbf_dom_inst                          none
% 19.43/2.98  --qbf_dom_pre_inst                      false
% 19.43/2.98  --qbf_sk_in                             false
% 19.43/2.98  --qbf_pred_elim                         true
% 19.43/2.98  --qbf_split                             512
% 19.43/2.98  
% 19.43/2.98  ------ BMC1 Options
% 19.43/2.98  
% 19.43/2.98  --bmc1_incremental                      false
% 19.43/2.98  --bmc1_axioms                           reachable_all
% 19.43/2.98  --bmc1_min_bound                        0
% 19.43/2.98  --bmc1_max_bound                        -1
% 19.43/2.98  --bmc1_max_bound_default                -1
% 19.43/2.98  --bmc1_symbol_reachability              true
% 19.43/2.98  --bmc1_property_lemmas                  false
% 19.43/2.98  --bmc1_k_induction                      false
% 19.43/2.98  --bmc1_non_equiv_states                 false
% 19.43/2.98  --bmc1_deadlock                         false
% 19.43/2.98  --bmc1_ucm                              false
% 19.43/2.98  --bmc1_add_unsat_core                   none
% 19.43/2.98  --bmc1_unsat_core_children              false
% 19.43/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/2.98  --bmc1_out_stat                         full
% 19.43/2.98  --bmc1_ground_init                      false
% 19.43/2.98  --bmc1_pre_inst_next_state              false
% 19.43/2.98  --bmc1_pre_inst_state                   false
% 19.43/2.98  --bmc1_pre_inst_reach_state             false
% 19.43/2.98  --bmc1_out_unsat_core                   false
% 19.43/2.98  --bmc1_aig_witness_out                  false
% 19.43/2.98  --bmc1_verbose                          false
% 19.43/2.98  --bmc1_dump_clauses_tptp                false
% 19.43/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.43/2.98  --bmc1_dump_file                        -
% 19.43/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.43/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.43/2.98  --bmc1_ucm_extend_mode                  1
% 19.43/2.98  --bmc1_ucm_init_mode                    2
% 19.43/2.98  --bmc1_ucm_cone_mode                    none
% 19.43/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.43/2.98  --bmc1_ucm_relax_model                  4
% 19.43/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.43/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/2.98  --bmc1_ucm_layered_model                none
% 19.43/2.98  --bmc1_ucm_max_lemma_size               10
% 19.43/2.98  
% 19.43/2.98  ------ AIG Options
% 19.43/2.98  
% 19.43/2.98  --aig_mode                              false
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation Options
% 19.43/2.98  
% 19.43/2.98  --instantiation_flag                    true
% 19.43/2.98  --inst_sos_flag                         true
% 19.43/2.98  --inst_sos_phase                        true
% 19.43/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel_side                     num_symb
% 19.43/2.98  --inst_solver_per_active                1400
% 19.43/2.98  --inst_solver_calls_frac                1.
% 19.43/2.98  --inst_passive_queue_type               priority_queues
% 19.43/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/2.98  --inst_passive_queues_freq              [25;2]
% 19.43/2.98  --inst_dismatching                      true
% 19.43/2.98  --inst_eager_unprocessed_to_passive     true
% 19.43/2.98  --inst_prop_sim_given                   true
% 19.43/2.98  --inst_prop_sim_new                     false
% 19.43/2.98  --inst_subs_new                         false
% 19.43/2.98  --inst_eq_res_simp                      false
% 19.43/2.98  --inst_subs_given                       false
% 19.43/2.98  --inst_orphan_elimination               true
% 19.43/2.98  --inst_learning_loop_flag               true
% 19.43/2.98  --inst_learning_start                   3000
% 19.43/2.98  --inst_learning_factor                  2
% 19.43/2.98  --inst_start_prop_sim_after_learn       3
% 19.43/2.98  --inst_sel_renew                        solver
% 19.43/2.98  --inst_lit_activity_flag                true
% 19.43/2.98  --inst_restr_to_given                   false
% 19.43/2.98  --inst_activity_threshold               500
% 19.43/2.98  --inst_out_proof                        true
% 19.43/2.98  
% 19.43/2.98  ------ Resolution Options
% 19.43/2.98  
% 19.43/2.98  --resolution_flag                       true
% 19.43/2.98  --res_lit_sel                           adaptive
% 19.43/2.98  --res_lit_sel_side                      none
% 19.43/2.98  --res_ordering                          kbo
% 19.43/2.98  --res_to_prop_solver                    active
% 19.43/2.98  --res_prop_simpl_new                    false
% 19.43/2.98  --res_prop_simpl_given                  true
% 19.43/2.98  --res_passive_queue_type                priority_queues
% 19.43/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/2.98  --res_passive_queues_freq               [15;5]
% 19.43/2.98  --res_forward_subs                      full
% 19.43/2.98  --res_backward_subs                     full
% 19.43/2.98  --res_forward_subs_resolution           true
% 19.43/2.98  --res_backward_subs_resolution          true
% 19.43/2.98  --res_orphan_elimination                true
% 19.43/2.98  --res_time_limit                        2.
% 19.43/2.98  --res_out_proof                         true
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Options
% 19.43/2.98  
% 19.43/2.98  --superposition_flag                    true
% 19.43/2.98  --sup_passive_queue_type                priority_queues
% 19.43/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.43/2.98  --demod_completeness_check              fast
% 19.43/2.98  --demod_use_ground                      true
% 19.43/2.98  --sup_to_prop_solver                    passive
% 19.43/2.98  --sup_prop_simpl_new                    true
% 19.43/2.98  --sup_prop_simpl_given                  true
% 19.43/2.98  --sup_fun_splitting                     true
% 19.43/2.98  --sup_smt_interval                      50000
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Simplification Setup
% 19.43/2.98  
% 19.43/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.43/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_immed_triv                        [TrivRules]
% 19.43/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_bw_main                     []
% 19.43/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_input_bw                          []
% 19.43/2.98  
% 19.43/2.98  ------ Combination Options
% 19.43/2.98  
% 19.43/2.98  --comb_res_mult                         3
% 19.43/2.98  --comb_sup_mult                         2
% 19.43/2.98  --comb_inst_mult                        10
% 19.43/2.98  
% 19.43/2.98  ------ Debug Options
% 19.43/2.98  
% 19.43/2.98  --dbg_backtrace                         false
% 19.43/2.98  --dbg_dump_prop_clauses                 false
% 19.43/2.98  --dbg_dump_prop_clauses_file            -
% 19.43/2.98  --dbg_out_stat                          false
% 19.43/2.98  ------ Parsing...
% 19.43/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.43/2.98  ------ Proving...
% 19.43/2.98  ------ Problem Properties 
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  clauses                                 16
% 19.43/2.98  conjectures                             3
% 19.43/2.98  EPR                                     3
% 19.43/2.98  Horn                                    16
% 19.43/2.98  unary                                   6
% 19.43/2.98  binary                                  7
% 19.43/2.98  lits                                    29
% 19.43/2.98  lits eq                                 8
% 19.43/2.98  fd_pure                                 0
% 19.43/2.98  fd_pseudo                               0
% 19.43/2.98  fd_cond                                 0
% 19.43/2.98  fd_pseudo_cond                          1
% 19.43/2.98  AC symbols                              0
% 19.43/2.98  
% 19.43/2.98  ------ Schedule dynamic 5 is on 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  ------ 
% 19.43/2.98  Current options:
% 19.43/2.98  ------ 
% 19.43/2.98  
% 19.43/2.98  ------ Input Options
% 19.43/2.98  
% 19.43/2.98  --out_options                           all
% 19.43/2.98  --tptp_safe_out                         true
% 19.43/2.98  --problem_path                          ""
% 19.43/2.98  --include_path                          ""
% 19.43/2.98  --clausifier                            res/vclausify_rel
% 19.43/2.98  --clausifier_options                    ""
% 19.43/2.98  --stdin                                 false
% 19.43/2.98  --stats_out                             all
% 19.43/2.98  
% 19.43/2.98  ------ General Options
% 19.43/2.98  
% 19.43/2.98  --fof                                   false
% 19.43/2.98  --time_out_real                         305.
% 19.43/2.98  --time_out_virtual                      -1.
% 19.43/2.98  --symbol_type_check                     false
% 19.43/2.98  --clausify_out                          false
% 19.43/2.98  --sig_cnt_out                           false
% 19.43/2.98  --trig_cnt_out                          false
% 19.43/2.98  --trig_cnt_out_tolerance                1.
% 19.43/2.98  --trig_cnt_out_sk_spl                   false
% 19.43/2.98  --abstr_cl_out                          false
% 19.43/2.98  
% 19.43/2.98  ------ Global Options
% 19.43/2.98  
% 19.43/2.98  --schedule                              default
% 19.43/2.98  --add_important_lit                     false
% 19.43/2.98  --prop_solver_per_cl                    1000
% 19.43/2.98  --min_unsat_core                        false
% 19.43/2.98  --soft_assumptions                      false
% 19.43/2.98  --soft_lemma_size                       3
% 19.43/2.98  --prop_impl_unit_size                   0
% 19.43/2.98  --prop_impl_unit                        []
% 19.43/2.98  --share_sel_clauses                     true
% 19.43/2.98  --reset_solvers                         false
% 19.43/2.98  --bc_imp_inh                            [conj_cone]
% 19.43/2.98  --conj_cone_tolerance                   3.
% 19.43/2.98  --extra_neg_conj                        none
% 19.43/2.98  --large_theory_mode                     true
% 19.43/2.98  --prolific_symb_bound                   200
% 19.43/2.98  --lt_threshold                          2000
% 19.43/2.98  --clause_weak_htbl                      true
% 19.43/2.98  --gc_record_bc_elim                     false
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing Options
% 19.43/2.98  
% 19.43/2.98  --preprocessing_flag                    true
% 19.43/2.98  --time_out_prep_mult                    0.1
% 19.43/2.98  --splitting_mode                        input
% 19.43/2.98  --splitting_grd                         true
% 19.43/2.98  --splitting_cvd                         false
% 19.43/2.98  --splitting_cvd_svl                     false
% 19.43/2.98  --splitting_nvd                         32
% 19.43/2.98  --sub_typing                            true
% 19.43/2.98  --prep_gs_sim                           true
% 19.43/2.98  --prep_unflatten                        true
% 19.43/2.98  --prep_res_sim                          true
% 19.43/2.98  --prep_upred                            true
% 19.43/2.98  --prep_sem_filter                       exhaustive
% 19.43/2.98  --prep_sem_filter_out                   false
% 19.43/2.98  --pred_elim                             true
% 19.43/2.98  --res_sim_input                         true
% 19.43/2.98  --eq_ax_congr_red                       true
% 19.43/2.98  --pure_diseq_elim                       true
% 19.43/2.98  --brand_transform                       false
% 19.43/2.98  --non_eq_to_eq                          false
% 19.43/2.98  --prep_def_merge                        true
% 19.43/2.98  --prep_def_merge_prop_impl              false
% 19.43/2.98  --prep_def_merge_mbd                    true
% 19.43/2.98  --prep_def_merge_tr_red                 false
% 19.43/2.98  --prep_def_merge_tr_cl                  false
% 19.43/2.98  --smt_preprocessing                     true
% 19.43/2.98  --smt_ac_axioms                         fast
% 19.43/2.98  --preprocessed_out                      false
% 19.43/2.98  --preprocessed_stats                    false
% 19.43/2.98  
% 19.43/2.98  ------ Abstraction refinement Options
% 19.43/2.98  
% 19.43/2.98  --abstr_ref                             []
% 19.43/2.98  --abstr_ref_prep                        false
% 19.43/2.98  --abstr_ref_until_sat                   false
% 19.43/2.98  --abstr_ref_sig_restrict                funpre
% 19.43/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.43/2.98  --abstr_ref_under                       []
% 19.43/2.98  
% 19.43/2.98  ------ SAT Options
% 19.43/2.98  
% 19.43/2.98  --sat_mode                              false
% 19.43/2.98  --sat_fm_restart_options                ""
% 19.43/2.98  --sat_gr_def                            false
% 19.43/2.98  --sat_epr_types                         true
% 19.43/2.98  --sat_non_cyclic_types                  false
% 19.43/2.98  --sat_finite_models                     false
% 19.43/2.98  --sat_fm_lemmas                         false
% 19.43/2.98  --sat_fm_prep                           false
% 19.43/2.98  --sat_fm_uc_incr                        true
% 19.43/2.98  --sat_out_model                         small
% 19.43/2.98  --sat_out_clauses                       false
% 19.43/2.98  
% 19.43/2.98  ------ QBF Options
% 19.43/2.98  
% 19.43/2.98  --qbf_mode                              false
% 19.43/2.98  --qbf_elim_univ                         false
% 19.43/2.98  --qbf_dom_inst                          none
% 19.43/2.98  --qbf_dom_pre_inst                      false
% 19.43/2.98  --qbf_sk_in                             false
% 19.43/2.98  --qbf_pred_elim                         true
% 19.43/2.98  --qbf_split                             512
% 19.43/2.98  
% 19.43/2.98  ------ BMC1 Options
% 19.43/2.98  
% 19.43/2.98  --bmc1_incremental                      false
% 19.43/2.98  --bmc1_axioms                           reachable_all
% 19.43/2.98  --bmc1_min_bound                        0
% 19.43/2.98  --bmc1_max_bound                        -1
% 19.43/2.98  --bmc1_max_bound_default                -1
% 19.43/2.98  --bmc1_symbol_reachability              true
% 19.43/2.98  --bmc1_property_lemmas                  false
% 19.43/2.98  --bmc1_k_induction                      false
% 19.43/2.98  --bmc1_non_equiv_states                 false
% 19.43/2.98  --bmc1_deadlock                         false
% 19.43/2.98  --bmc1_ucm                              false
% 19.43/2.98  --bmc1_add_unsat_core                   none
% 19.43/2.98  --bmc1_unsat_core_children              false
% 19.43/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.43/2.98  --bmc1_out_stat                         full
% 19.43/2.98  --bmc1_ground_init                      false
% 19.43/2.98  --bmc1_pre_inst_next_state              false
% 19.43/2.98  --bmc1_pre_inst_state                   false
% 19.43/2.98  --bmc1_pre_inst_reach_state             false
% 19.43/2.98  --bmc1_out_unsat_core                   false
% 19.43/2.98  --bmc1_aig_witness_out                  false
% 19.43/2.98  --bmc1_verbose                          false
% 19.43/2.98  --bmc1_dump_clauses_tptp                false
% 19.43/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.43/2.98  --bmc1_dump_file                        -
% 19.43/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.43/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.43/2.98  --bmc1_ucm_extend_mode                  1
% 19.43/2.98  --bmc1_ucm_init_mode                    2
% 19.43/2.98  --bmc1_ucm_cone_mode                    none
% 19.43/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.43/2.98  --bmc1_ucm_relax_model                  4
% 19.43/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.43/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.43/2.98  --bmc1_ucm_layered_model                none
% 19.43/2.98  --bmc1_ucm_max_lemma_size               10
% 19.43/2.98  
% 19.43/2.98  ------ AIG Options
% 19.43/2.98  
% 19.43/2.98  --aig_mode                              false
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation Options
% 19.43/2.98  
% 19.43/2.98  --instantiation_flag                    true
% 19.43/2.98  --inst_sos_flag                         true
% 19.43/2.98  --inst_sos_phase                        true
% 19.43/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.43/2.98  --inst_lit_sel_side                     none
% 19.43/2.98  --inst_solver_per_active                1400
% 19.43/2.98  --inst_solver_calls_frac                1.
% 19.43/2.98  --inst_passive_queue_type               priority_queues
% 19.43/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.43/2.98  --inst_passive_queues_freq              [25;2]
% 19.43/2.98  --inst_dismatching                      true
% 19.43/2.98  --inst_eager_unprocessed_to_passive     true
% 19.43/2.98  --inst_prop_sim_given                   true
% 19.43/2.98  --inst_prop_sim_new                     false
% 19.43/2.98  --inst_subs_new                         false
% 19.43/2.98  --inst_eq_res_simp                      false
% 19.43/2.98  --inst_subs_given                       false
% 19.43/2.98  --inst_orphan_elimination               true
% 19.43/2.98  --inst_learning_loop_flag               true
% 19.43/2.98  --inst_learning_start                   3000
% 19.43/2.98  --inst_learning_factor                  2
% 19.43/2.98  --inst_start_prop_sim_after_learn       3
% 19.43/2.98  --inst_sel_renew                        solver
% 19.43/2.98  --inst_lit_activity_flag                true
% 19.43/2.98  --inst_restr_to_given                   false
% 19.43/2.98  --inst_activity_threshold               500
% 19.43/2.98  --inst_out_proof                        true
% 19.43/2.98  
% 19.43/2.98  ------ Resolution Options
% 19.43/2.98  
% 19.43/2.98  --resolution_flag                       false
% 19.43/2.98  --res_lit_sel                           adaptive
% 19.43/2.98  --res_lit_sel_side                      none
% 19.43/2.98  --res_ordering                          kbo
% 19.43/2.98  --res_to_prop_solver                    active
% 19.43/2.98  --res_prop_simpl_new                    false
% 19.43/2.98  --res_prop_simpl_given                  true
% 19.43/2.98  --res_passive_queue_type                priority_queues
% 19.43/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.43/2.98  --res_passive_queues_freq               [15;5]
% 19.43/2.98  --res_forward_subs                      full
% 19.43/2.98  --res_backward_subs                     full
% 19.43/2.98  --res_forward_subs_resolution           true
% 19.43/2.98  --res_backward_subs_resolution          true
% 19.43/2.98  --res_orphan_elimination                true
% 19.43/2.98  --res_time_limit                        2.
% 19.43/2.98  --res_out_proof                         true
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Options
% 19.43/2.98  
% 19.43/2.98  --superposition_flag                    true
% 19.43/2.98  --sup_passive_queue_type                priority_queues
% 19.43/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.43/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.43/2.98  --demod_completeness_check              fast
% 19.43/2.98  --demod_use_ground                      true
% 19.43/2.98  --sup_to_prop_solver                    passive
% 19.43/2.98  --sup_prop_simpl_new                    true
% 19.43/2.98  --sup_prop_simpl_given                  true
% 19.43/2.98  --sup_fun_splitting                     true
% 19.43/2.98  --sup_smt_interval                      50000
% 19.43/2.98  
% 19.43/2.98  ------ Superposition Simplification Setup
% 19.43/2.98  
% 19.43/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.43/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.43/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.43/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.43/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_immed_triv                        [TrivRules]
% 19.43/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_immed_bw_main                     []
% 19.43/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.43/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.43/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.43/2.98  --sup_input_bw                          []
% 19.43/2.98  
% 19.43/2.98  ------ Combination Options
% 19.43/2.98  
% 19.43/2.98  --comb_res_mult                         3
% 19.43/2.98  --comb_sup_mult                         2
% 19.43/2.98  --comb_inst_mult                        10
% 19.43/2.98  
% 19.43/2.98  ------ Debug Options
% 19.43/2.98  
% 19.43/2.98  --dbg_backtrace                         false
% 19.43/2.98  --dbg_dump_prop_clauses                 false
% 19.43/2.98  --dbg_dump_prop_clauses_file            -
% 19.43/2.98  --dbg_out_stat                          false
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  ------ Proving...
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  % SZS status Theorem for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  fof(f13,conjecture,(
% 19.43/2.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f14,negated_conjecture,(
% 19.43/2.98    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.43/2.98    inference(negated_conjecture,[],[f13])).
% 19.43/2.98  
% 19.43/2.98  fof(f26,plain,(
% 19.43/2.98    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f14])).
% 19.43/2.98  
% 19.43/2.98  fof(f27,plain,(
% 19.43/2.98    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 19.43/2.98    inference(flattening,[],[f26])).
% 19.43/2.98  
% 19.43/2.98  fof(f30,plain,(
% 19.43/2.98    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 19.43/2.98    introduced(choice_axiom,[])).
% 19.43/2.98  
% 19.43/2.98  fof(f31,plain,(
% 19.43/2.98    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 19.43/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).
% 19.43/2.98  
% 19.43/2.98  fof(f46,plain,(
% 19.43/2.98    v1_relat_1(sK1)),
% 19.43/2.98    inference(cnf_transformation,[],[f31])).
% 19.43/2.98  
% 19.43/2.98  fof(f10,axiom,(
% 19.43/2.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f22,plain,(
% 19.43/2.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 19.43/2.98    inference(ennf_transformation,[],[f10])).
% 19.43/2.98  
% 19.43/2.98  fof(f43,plain,(
% 19.43/2.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f22])).
% 19.43/2.98  
% 19.43/2.98  fof(f8,axiom,(
% 19.43/2.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f20,plain,(
% 19.43/2.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.43/2.98    inference(ennf_transformation,[],[f8])).
% 19.43/2.98  
% 19.43/2.98  fof(f41,plain,(
% 19.43/2.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f20])).
% 19.43/2.98  
% 19.43/2.98  fof(f2,axiom,(
% 19.43/2.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f28,plain,(
% 19.43/2.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.43/2.98    inference(nnf_transformation,[],[f2])).
% 19.43/2.98  
% 19.43/2.98  fof(f29,plain,(
% 19.43/2.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.43/2.98    inference(flattening,[],[f28])).
% 19.43/2.98  
% 19.43/2.98  fof(f33,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.43/2.98    inference(cnf_transformation,[],[f29])).
% 19.43/2.98  
% 19.43/2.98  fof(f50,plain,(
% 19.43/2.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.43/2.98    inference(equality_resolution,[],[f33])).
% 19.43/2.98  
% 19.43/2.98  fof(f11,axiom,(
% 19.43/2.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f23,plain,(
% 19.43/2.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f11])).
% 19.43/2.98  
% 19.43/2.98  fof(f24,plain,(
% 19.43/2.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 19.43/2.98    inference(flattening,[],[f23])).
% 19.43/2.98  
% 19.43/2.98  fof(f44,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f24])).
% 19.43/2.98  
% 19.43/2.98  fof(f12,axiom,(
% 19.43/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f25,plain,(
% 19.43/2.98    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.43/2.98    inference(ennf_transformation,[],[f12])).
% 19.43/2.98  
% 19.43/2.98  fof(f45,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f25])).
% 19.43/2.98  
% 19.43/2.98  fof(f1,axiom,(
% 19.43/2.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f32,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f1])).
% 19.43/2.98  
% 19.43/2.98  fof(f9,axiom,(
% 19.43/2.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f21,plain,(
% 19.43/2.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f9])).
% 19.43/2.98  
% 19.43/2.98  fof(f42,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f21])).
% 19.43/2.98  
% 19.43/2.98  fof(f5,axiom,(
% 19.43/2.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f38,plain,(
% 19.43/2.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f5])).
% 19.43/2.98  
% 19.43/2.98  fof(f6,axiom,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f17,plain,(
% 19.43/2.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f6])).
% 19.43/2.98  
% 19.43/2.98  fof(f39,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f17])).
% 19.43/2.98  
% 19.43/2.98  fof(f47,plain,(
% 19.43/2.98    r1_tarski(sK0,k1_relat_1(sK1))),
% 19.43/2.98    inference(cnf_transformation,[],[f31])).
% 19.43/2.98  
% 19.43/2.98  fof(f4,axiom,(
% 19.43/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f16,plain,(
% 19.43/2.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.43/2.98    inference(ennf_transformation,[],[f4])).
% 19.43/2.98  
% 19.43/2.98  fof(f37,plain,(
% 19.43/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f16])).
% 19.43/2.98  
% 19.43/2.98  fof(f3,axiom,(
% 19.43/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f15,plain,(
% 19.43/2.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 19.43/2.98    inference(ennf_transformation,[],[f3])).
% 19.43/2.98  
% 19.43/2.98  fof(f36,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f15])).
% 19.43/2.98  
% 19.43/2.98  fof(f7,axiom,(
% 19.43/2.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 19.43/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.43/2.98  
% 19.43/2.98  fof(f18,plain,(
% 19.43/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 19.43/2.98    inference(ennf_transformation,[],[f7])).
% 19.43/2.98  
% 19.43/2.98  fof(f19,plain,(
% 19.43/2.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 19.43/2.98    inference(flattening,[],[f18])).
% 19.43/2.98  
% 19.43/2.98  fof(f40,plain,(
% 19.43/2.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.43/2.98    inference(cnf_transformation,[],[f19])).
% 19.43/2.98  
% 19.43/2.98  fof(f48,plain,(
% 19.43/2.98    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 19.43/2.98    inference(cnf_transformation,[],[f31])).
% 19.43/2.98  
% 19.43/2.98  cnf(c_16,negated_conjecture,
% 19.43/2.98      ( v1_relat_1(sK1) ),
% 19.43/2.98      inference(cnf_transformation,[],[f46]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_544,plain,
% 19.43/2.98      ( v1_relat_1(sK1) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_11,plain,
% 19.43/2.98      ( ~ v1_relat_1(X0)
% 19.43/2.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f43]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_549,plain,
% 19.43/2.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1159,plain,
% 19.43/2.98      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_549]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_9,plain,
% 19.43/2.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.43/2.98      inference(cnf_transformation,[],[f41]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_551,plain,
% 19.43/2.98      ( v1_relat_1(X0) != iProver_top
% 19.43/2.98      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_3,plain,
% 19.43/2.98      ( r1_tarski(X0,X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f50]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_557,plain,
% 19.43/2.98      ( r1_tarski(X0,X0) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_12,plain,
% 19.43/2.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 19.43/2.98      | ~ v1_relat_1(X0)
% 19.43/2.98      | k7_relat_1(X0,X1) = X0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f44]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_548,plain,
% 19.43/2.98      ( k7_relat_1(X0,X1) = X0
% 19.43/2.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1677,plain,
% 19.43/2.98      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_557,c_548]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_7131,plain,
% 19.43/2.98      ( k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(X0,X1)
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_551,c_1677]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_87245,plain,
% 19.43/2.98      ( k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_7131]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_13,plain,
% 19.43/2.98      ( ~ v1_relat_1(X0)
% 19.43/2.98      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 19.43/2.98      inference(cnf_transformation,[],[f45]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_547,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1061,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2),X3) = k3_xboole_0(X2,k10_relat_1(k7_relat_1(X0,X1),X3))
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_551,c_547]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2684,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_1061]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1062,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_547]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2685,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_2684,c_1062]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_90312,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_87245,c_2685]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_90313,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k10_relat_1(sK1,X1))) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_90312,c_1062]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_90977,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(sK1))) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1159,c_90313]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91064,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k3_xboole_0(X0,k1_relat_1(sK1))) = k3_xboole_0(X0,k1_relat_1(sK1)) ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_90977,c_1159]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_0,plain,
% 19.43/2.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f32]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1158,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_551,c_549]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_3928,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_1158]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_10,plain,
% 19.43/2.98      ( ~ v1_relat_1(X0)
% 19.43/2.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.43/2.98      inference(cnf_transformation,[],[f42]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_550,plain,
% 19.43/2.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 19.43/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1270,plain,
% 19.43/2.98      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_544,c_550]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_3929,plain,
% 19.43/2.98      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_3928,c_1270]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4548,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1062,c_3929]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 19.43/2.98      inference(cnf_transformation,[],[f38]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_554,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_7,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.43/2.98      inference(cnf_transformation,[],[f39]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_553,plain,
% 19.43/2.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1069,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_554,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2810,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_1069]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2843,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_2810,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_15,negated_conjecture,
% 19.43/2.98      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 19.43/2.98      inference(cnf_transformation,[],[f47]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_545,plain,
% 19.43/2.98      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_5,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.43/2.98      inference(cnf_transformation,[],[f37]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_555,plain,
% 19.43/2.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1152,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_554,c_555]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4,plain,
% 19.43/2.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.43/2.98      inference(cnf_transformation,[],[f36]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_556,plain,
% 19.43/2.98      ( r1_tarski(X0,X1) = iProver_top
% 19.43/2.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1823,plain,
% 19.43/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.43/2.98      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1152,c_556]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_9290,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
% 19.43/2.98      | r1_tarski(X0,X2) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1823,c_555]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_25810,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_545,c_9290]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_878,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_554]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1154,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_878,c_555]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1820,plain,
% 19.43/2.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_557,c_556]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2150,plain,
% 19.43/2.98      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1820,c_556]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6097,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1154,c_2150]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_43725,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_25810,c_6097]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_44373,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_43725,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_48021,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k1_relat_1(sK1)) = k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_2843,c_44373]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_48123,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_48021,c_44373]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1071,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_878,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4168,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1071,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_48124,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(X1,sK0)) = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_48123,c_4168]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_53229,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(sK0,X1)) = k3_xboole_0(k3_xboole_0(X1,sK0),X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_48124]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_25809,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X0) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_554,c_9290]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_55096,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X1) = X1 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_53229,c_25809]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_59285,plain,
% 19.43/2.98      ( k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X1) = X1 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_55096]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_59468,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X1) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_59285,c_1820]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_63610,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),X1),X0) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_2810,c_59468]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_64133,plain,
% 19.43/2.98      ( r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),X0) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_63610]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_64216,plain,
% 19.43/2.98      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,X0))),X0) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_4548,c_64133]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1962,plain,
% 19.43/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.43/2.98      | r1_tarski(k3_xboole_0(X2,X0),X1) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1154,c_556]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_8,plain,
% 19.43/2.98      ( ~ r1_tarski(X0,X1)
% 19.43/2.98      | ~ r1_tarski(X2,X1)
% 19.43/2.98      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.43/2.98      inference(cnf_transformation,[],[f40]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_552,plain,
% 19.43/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.43/2.98      | r1_tarski(X2,X1) != iProver_top
% 19.43/2.98      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1948,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,X1)
% 19.43/2.98      | r1_tarski(X0,X2) != iProver_top
% 19.43/2.98      | r1_tarski(X1,X2) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_552,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_20480,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(sK0,X0),k1_relat_1(sK1)) = k2_xboole_0(sK0,X0)
% 19.43/2.98      | r1_tarski(X0,k1_relat_1(sK1)) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_545,c_1948]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_21547,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,X1)),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,X1))
% 19.43/2.98      | r1_tarski(X1,k1_relat_1(sK1)) != iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1962,c_20480]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_65206,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))))),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))))) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_64216,c_21547]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1070,plain,
% 19.43/2.98      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_545,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_65209,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))) ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_65206,c_1070]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_65661,plain,
% 19.43/2.98      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),X0)),k1_relat_1(sK1)) = k2_xboole_0(sK0,k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,sK0)))) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_0,c_65209]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91210,plain,
% 19.43/2.98      ( k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,sK0)))) = k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(sK1))),k1_relat_1(sK1)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_91064,c_65661]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91240,plain,
% 19.43/2.98      ( k2_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))) = k3_xboole_0(k2_xboole_0(sK0,sK0),k1_relat_1(sK1)) ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_91210,c_1070]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_1151,plain,
% 19.43/2.98      ( k2_xboole_0(X0,X0) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_557,c_555]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2821,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1069,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4553,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_4548,c_2821]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4566,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.43/2.98      inference(demodulation,[status(thm)],[c_4553,c_4548]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91241,plain,
% 19.43/2.98      ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0 ),
% 19.43/2.98      inference(demodulation,
% 19.43/2.98                [status(thm)],
% 19.43/2.98                [c_91240,c_1070,c_1151,c_4566]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4557,plain,
% 19.43/2.98      ( k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_4548,c_1152]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6104,plain,
% 19.43/2.98      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = X0 ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_2150,c_553]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_6380,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k2_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_4557,c_6104]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91797,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_91241,c_6380]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_54915,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,sK0),X1) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_53229,c_0]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_57030,plain,
% 19.43/2.98      ( k3_xboole_0(k3_xboole_0(X0,sK0),X0) = k3_xboole_0(sK0,X0) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_54915,c_1071]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91167,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k3_xboole_0(sK0,k1_relat_1(sK1))) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_57030,c_91064]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2833,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_1070,c_2810]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_2849,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(sK1),sK0) = sK0 ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_2833,c_1070]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91267,plain,
% 19.43/2.98      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) = sK0 ),
% 19.43/2.98      inference(light_normalisation,
% 19.43/2.98                [status(thm)],
% 19.43/2.98                [c_91167,c_1070,c_2849]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91836,plain,
% 19.43/2.98      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 19.43/2.98      inference(light_normalisation,[status(thm)],[c_91797,c_91267]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_4558,plain,
% 19.43/2.98      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_4548,c_878]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_91919,plain,
% 19.43/2.98      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 19.43/2.98      inference(superposition,[status(thm)],[c_91836,c_4558]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_14,negated_conjecture,
% 19.43/2.98      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 19.43/2.98      inference(cnf_transformation,[],[f48]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(c_19,plain,
% 19.43/2.98      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 19.43/2.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.43/2.98  
% 19.43/2.98  cnf(contradiction,plain,
% 19.43/2.98      ( $false ),
% 19.43/2.98      inference(minisat,[status(thm)],[c_91919,c_19]) ).
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.43/2.98  
% 19.43/2.98  ------                               Statistics
% 19.43/2.98  
% 19.43/2.98  ------ General
% 19.43/2.98  
% 19.43/2.98  abstr_ref_over_cycles:                  0
% 19.43/2.98  abstr_ref_under_cycles:                 0
% 19.43/2.98  gc_basic_clause_elim:                   0
% 19.43/2.98  forced_gc_time:                         0
% 19.43/2.98  parsing_time:                           0.006
% 19.43/2.98  unif_index_cands_time:                  0.
% 19.43/2.98  unif_index_add_time:                    0.
% 19.43/2.98  orderings_time:                         0.
% 19.43/2.98  out_proof_time:                         0.012
% 19.43/2.98  total_time:                             2.185
% 19.43/2.98  num_of_symbols:                         42
% 19.43/2.98  num_of_terms:                           84862
% 19.43/2.98  
% 19.43/2.98  ------ Preprocessing
% 19.43/2.98  
% 19.43/2.98  num_of_splits:                          0
% 19.43/2.98  num_of_split_atoms:                     0
% 19.43/2.98  num_of_reused_defs:                     0
% 19.43/2.98  num_eq_ax_congr_red:                    15
% 19.43/2.98  num_of_sem_filtered_clauses:            1
% 19.43/2.98  num_of_subtypes:                        0
% 19.43/2.98  monotx_restored_types:                  0
% 19.43/2.98  sat_num_of_epr_types:                   0
% 19.43/2.98  sat_num_of_non_cyclic_types:            0
% 19.43/2.98  sat_guarded_non_collapsed_types:        0
% 19.43/2.98  num_pure_diseq_elim:                    0
% 19.43/2.98  simp_replaced_by:                       0
% 19.43/2.98  res_preprocessed:                       83
% 19.43/2.98  prep_upred:                             0
% 19.43/2.98  prep_unflattend:                        0
% 19.43/2.98  smt_new_axioms:                         0
% 19.43/2.98  pred_elim_cands:                        2
% 19.43/2.98  pred_elim:                              0
% 19.43/2.98  pred_elim_cl:                           0
% 19.43/2.98  pred_elim_cycles:                       2
% 19.43/2.98  merged_defs:                            0
% 19.43/2.98  merged_defs_ncl:                        0
% 19.43/2.98  bin_hyper_res:                          0
% 19.43/2.98  prep_cycles:                            4
% 19.43/2.98  pred_elim_time:                         0.
% 19.43/2.98  splitting_time:                         0.
% 19.43/2.98  sem_filter_time:                        0.
% 19.43/2.98  monotx_time:                            0.
% 19.43/2.98  subtype_inf_time:                       0.
% 19.43/2.98  
% 19.43/2.98  ------ Problem properties
% 19.43/2.98  
% 19.43/2.98  clauses:                                16
% 19.43/2.98  conjectures:                            3
% 19.43/2.98  epr:                                    3
% 19.43/2.98  horn:                                   16
% 19.43/2.98  ground:                                 3
% 19.43/2.98  unary:                                  6
% 19.43/2.98  binary:                                 7
% 19.43/2.98  lits:                                   29
% 19.43/2.98  lits_eq:                                8
% 19.43/2.98  fd_pure:                                0
% 19.43/2.98  fd_pseudo:                              0
% 19.43/2.98  fd_cond:                                0
% 19.43/2.98  fd_pseudo_cond:                         1
% 19.43/2.98  ac_symbols:                             0
% 19.43/2.98  
% 19.43/2.98  ------ Propositional Solver
% 19.43/2.98  
% 19.43/2.98  prop_solver_calls:                      36
% 19.43/2.98  prop_fast_solver_calls:                 894
% 19.43/2.98  smt_solver_calls:                       0
% 19.43/2.98  smt_fast_solver_calls:                  0
% 19.43/2.98  prop_num_of_clauses:                    28362
% 19.43/2.98  prop_preprocess_simplified:             35409
% 19.43/2.98  prop_fo_subsumed:                       1
% 19.43/2.98  prop_solver_time:                       0.
% 19.43/2.98  smt_solver_time:                        0.
% 19.43/2.98  smt_fast_solver_time:                   0.
% 19.43/2.98  prop_fast_solver_time:                  0.
% 19.43/2.98  prop_unsat_core_time:                   0.003
% 19.43/2.98  
% 19.43/2.98  ------ QBF
% 19.43/2.98  
% 19.43/2.98  qbf_q_res:                              0
% 19.43/2.98  qbf_num_tautologies:                    0
% 19.43/2.98  qbf_prep_cycles:                        0
% 19.43/2.98  
% 19.43/2.98  ------ BMC1
% 19.43/2.98  
% 19.43/2.98  bmc1_current_bound:                     -1
% 19.43/2.98  bmc1_last_solved_bound:                 -1
% 19.43/2.98  bmc1_unsat_core_size:                   -1
% 19.43/2.98  bmc1_unsat_core_parents_size:           -1
% 19.43/2.98  bmc1_merge_next_fun:                    0
% 19.43/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.43/2.98  
% 19.43/2.98  ------ Instantiation
% 19.43/2.98  
% 19.43/2.98  inst_num_of_clauses:                    6184
% 19.43/2.98  inst_num_in_passive:                    1173
% 19.43/2.98  inst_num_in_active:                     2095
% 19.43/2.98  inst_num_in_unprocessed:                2919
% 19.43/2.98  inst_num_of_loops:                      2290
% 19.43/2.98  inst_num_of_learning_restarts:          0
% 19.43/2.98  inst_num_moves_active_passive:          183
% 19.43/2.98  inst_lit_activity:                      0
% 19.43/2.98  inst_lit_activity_moves:                2
% 19.43/2.98  inst_num_tautologies:                   0
% 19.43/2.98  inst_num_prop_implied:                  0
% 19.43/2.98  inst_num_existing_simplified:           0
% 19.43/2.98  inst_num_eq_res_simplified:             0
% 19.43/2.98  inst_num_child_elim:                    0
% 19.43/2.98  inst_num_of_dismatching_blockings:      14041
% 19.43/2.98  inst_num_of_non_proper_insts:           9805
% 19.43/2.98  inst_num_of_duplicates:                 0
% 19.43/2.98  inst_inst_num_from_inst_to_res:         0
% 19.43/2.98  inst_dismatching_checking_time:         0.
% 19.43/2.98  
% 19.43/2.98  ------ Resolution
% 19.43/2.98  
% 19.43/2.98  res_num_of_clauses:                     0
% 19.43/2.98  res_num_in_passive:                     0
% 19.43/2.98  res_num_in_active:                      0
% 19.43/2.98  res_num_of_loops:                       87
% 19.43/2.98  res_forward_subset_subsumed:            1151
% 19.43/2.98  res_backward_subset_subsumed:           36
% 19.43/2.98  res_forward_subsumed:                   0
% 19.43/2.98  res_backward_subsumed:                  0
% 19.43/2.98  res_forward_subsumption_resolution:     0
% 19.43/2.98  res_backward_subsumption_resolution:    0
% 19.43/2.98  res_clause_to_clause_subsumption:       38370
% 19.43/2.98  res_orphan_elimination:                 0
% 19.43/2.98  res_tautology_del:                      393
% 19.43/2.98  res_num_eq_res_simplified:              0
% 19.43/2.98  res_num_sel_changes:                    0
% 19.43/2.98  res_moves_from_active_to_pass:          0
% 19.43/2.98  
% 19.43/2.98  ------ Superposition
% 19.43/2.98  
% 19.43/2.98  sup_time_total:                         0.
% 19.43/2.98  sup_time_generating:                    0.
% 19.43/2.98  sup_time_sim_full:                      0.
% 19.43/2.98  sup_time_sim_immed:                     0.
% 19.43/2.98  
% 19.43/2.98  sup_num_of_clauses:                     3221
% 19.43/2.98  sup_num_in_active:                      410
% 19.43/2.98  sup_num_in_passive:                     2811
% 19.43/2.98  sup_num_of_loops:                       457
% 19.43/2.98  sup_fw_superposition:                   11220
% 19.43/2.98  sup_bw_superposition:                   11779
% 19.43/2.98  sup_immediate_simplified:               8381
% 19.43/2.98  sup_given_eliminated:                   1
% 19.43/2.98  comparisons_done:                       0
% 19.43/2.98  comparisons_avoided:                    0
% 19.43/2.98  
% 19.43/2.98  ------ Simplifications
% 19.43/2.98  
% 19.43/2.98  
% 19.43/2.98  sim_fw_subset_subsumed:                 198
% 19.43/2.98  sim_bw_subset_subsumed:                 24
% 19.43/2.98  sim_fw_subsumed:                        1950
% 19.43/2.98  sim_bw_subsumed:                        22
% 19.43/2.98  sim_fw_subsumption_res:                 0
% 19.43/2.98  sim_bw_subsumption_res:                 0
% 19.43/2.98  sim_tautology_del:                      223
% 19.43/2.98  sim_eq_tautology_del:                   1352
% 19.43/2.98  sim_eq_res_simp:                        0
% 19.43/2.98  sim_fw_demodulated:                     4155
% 19.43/2.98  sim_bw_demodulated:                     43
% 19.43/2.98  sim_light_normalised:                   2669
% 19.43/2.98  sim_joinable_taut:                      0
% 19.43/2.98  sim_joinable_simp:                      0
% 19.43/2.98  sim_ac_normalised:                      0
% 19.43/2.98  sim_smt_subsumption:                    0
% 19.43/2.98  
%------------------------------------------------------------------------------
