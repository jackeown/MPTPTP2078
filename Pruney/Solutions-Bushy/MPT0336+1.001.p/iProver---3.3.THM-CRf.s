%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:02 EST 2020

% Result     : Theorem 14.83s
% Output     : CNFRefutation 14.83s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 570 expanded)
%              Number of clauses        :   79 ( 235 expanded)
%              Number of leaves         :   12 ( 119 expanded)
%              Depth                    :   21
%              Number of atoms          :  179 (1206 expanded)
%              Number of equality atoms :  102 ( 447 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f22])).

fof(f36,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_136,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_137,plain,
    ( r1_tarski(k1_tarski(sK3),sK2) ),
    inference(unflattening,[status(thm)],[c_136])).

cnf(c_283,plain,
    ( r1_tarski(k1_tarski(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_284,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_285,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1488,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),X0) = iProver_top
    | r1_tarski(k1_tarski(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_285])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_286,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2731,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),X0) = X0
    | r1_tarski(k1_tarski(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_286])).

cnf(c_16649,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_283,c_2731])).

cnf(c_16859,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_0,c_16649])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_778,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_15188,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_4,c_778])).

cnf(c_65918,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) = k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_16859,c_15188])).

cnf(c_788,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_76,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_151,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_76,c_12])).

cnf(c_152,plain,
    ( k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_323,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_4204,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_152,c_323])).

cnf(c_66964,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_65918,c_788,c_4204])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_66965,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_66964,c_8])).

cnf(c_685,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_961,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_685])).

cnf(c_1610,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_152,c_961])).

cnf(c_1925,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_1610,c_7])).

cnf(c_1928,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1610,c_1])).

cnf(c_1938,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1928,c_152])).

cnf(c_1973,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1925,c_1938])).

cnf(c_2600,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,sK2)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1973])).

cnf(c_69540,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_66965,c_2600])).

cnf(c_4203,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_323])).

cnf(c_686,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_152,c_7])).

cnf(c_1110,plain,
    ( k3_xboole_0(k1_xboole_0,sK1) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_4,c_686])).

cnf(c_1128,plain,
    ( k3_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1110,c_152])).

cnf(c_4217,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1128,c_323])).

cnf(c_4875,plain,
    ( k3_xboole_0(sK2,k2_xboole_0(X0,k3_xboole_0(X1,sK1))) = k2_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4204,c_10])).

cnf(c_18650,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK2),k3_xboole_0(sK0,k1_xboole_0)) = k3_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_16859,c_4875])).

cnf(c_18652,plain,
    ( k2_xboole_0(sK2,k3_xboole_0(sK0,k1_xboole_0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_18650,c_4])).

cnf(c_324,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_6044,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_152,c_324])).

cnf(c_15232,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,k3_xboole_0(sK2,X1))) = k2_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6044,c_778])).

cnf(c_23947,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),sK1),k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(sK1,k3_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_778,c_15232])).

cnf(c_24192,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),sK1),k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23947,c_6044])).

cnf(c_27844,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_24192])).

cnf(c_27991,plain,
    ( k3_xboole_0(k2_xboole_0(sK2,X0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_27844,c_152])).

cnf(c_575,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_27992,plain,
    ( k3_xboole_0(k2_xboole_0(sK2,X0),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_27991,c_575])).

cnf(c_28049,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18652,c_27992])).

cnf(c_964,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_152,c_685])).

cnf(c_981,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_964,c_152])).

cnf(c_28175,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_28049,c_981])).

cnf(c_29985,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28175,c_7])).

cnf(c_30050,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29985,c_4])).

cnf(c_69552,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_69540,c_4203,c_4217,c_30050])).

cnf(c_1929,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(sK1,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1610,c_10])).

cnf(c_1964,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,sK2)) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1929,c_1938])).

cnf(c_1966,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,sK2)) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1964,c_8])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_74,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_146,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(sK0,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_74,c_11])).

cnf(c_147,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_200,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_147,c_7,c_1])).

cnf(c_3353,plain,
    ( k3_xboole_0(sK1,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1966,c_200])).

cnf(c_3562,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3353])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69552,c_3562])).


%------------------------------------------------------------------------------
