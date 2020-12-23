%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:46 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  147 (1639 expanded)
%              Number of clauses        :  102 ( 661 expanded)
%              Number of leaves         :   18 ( 401 expanded)
%              Depth                    :   26
%              Number of atoms          :  199 (2687 expanded)
%              Number of equality atoms :  161 (1936 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).

fof(f43,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f45,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f41,f41])).

fof(f46,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_181,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_44082,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_168,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_18,c_14,c_0])).

cnf(c_178,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_2415,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_168,c_178])).

cnf(c_12,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_426,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_2734,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(superposition,[status(thm)],[c_2415,c_426])).

cnf(c_2720,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_2415])).

cnf(c_3911,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_2720,c_426])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_431,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_434,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_431,c_10])).

cnf(c_853,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_168,c_14])).

cnf(c_1115,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_853,c_14])).

cnf(c_1950,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_434,c_1115])).

cnf(c_1955,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1950,c_168])).

cnf(c_2159,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1955,c_12])).

cnf(c_5195,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) = k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2159,c_10])).

cnf(c_2160,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1955,c_434])).

cnf(c_13,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_176,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_11])).

cnf(c_823,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_176])).

cnf(c_824,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_823,c_10])).

cnf(c_2161,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1955,c_824])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_71,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_139,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_71,c_6])).

cnf(c_2376,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_2161,c_139])).

cnf(c_5442,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2160,c_2376])).

cnf(c_5454,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_5442,c_14])).

cnf(c_5476,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
    inference(demodulation,[status(thm)],[c_5195,c_5454])).

cnf(c_5186,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_2159])).

cnf(c_2154,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_1955])).

cnf(c_2333,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_2154,c_12])).

cnf(c_2768,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2415,c_434])).

cnf(c_2963,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[status(thm)],[c_2768,c_434])).

cnf(c_2418,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_434,c_178])).

cnf(c_2973,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2963,c_1955,c_2418])).

cnf(c_3070,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_2973,c_14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_127,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_128,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_355,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_128,c_139])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_147,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_148,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_167,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_148,c_14,c_0])).

cnf(c_359,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_355,c_167])).

cnf(c_809,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_359,c_13])).

cnf(c_951,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_168,c_824])).

cnf(c_2621,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_809,c_951])).

cnf(c_2846,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2621,c_10])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2848,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_2846,c_7])).

cnf(c_3072,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_3070,c_2848])).

cnf(c_5204,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5186,c_2333,c_3072])).

cnf(c_945,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_824])).

cnf(c_5205,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5204,c_945])).

cnf(c_5477,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK0) = k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5476,c_5205])).

cnf(c_1620,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_945,c_10])).

cnf(c_1623,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1620,c_7])).

cnf(c_4636,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1623])).

cnf(c_5478,plain,
    ( k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5477,c_7,c_4636])).

cnf(c_5980,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_5478,c_12])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_133,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_356,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_133,c_139])).

cnf(c_358,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_356,c_167])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1751,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_426,c_1])).

cnf(c_428,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_12])).

cnf(c_1755,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1751,c_11,c_428,c_945])).

cnf(c_1773,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_358,c_1755])).

cnf(c_4377,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_428,c_428,c_1755])).

cnf(c_4415,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK2,sK0),sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2768,c_4377])).

cnf(c_429,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_168,c_12])).

cnf(c_4476,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4415,c_429,c_3072])).

cnf(c_810,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_358,c_13])).

cnf(c_3487,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_2848,c_810])).

cnf(c_3489,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3487,c_358])).

cnf(c_4477,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_4476,c_3489])).

cnf(c_6000,plain,
    ( sK0 = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5980,c_1773,c_4477])).

cnf(c_6142,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK3)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(light_normalisation,[status(thm)],[c_2734,c_3911,c_6000])).

cnf(c_2442,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_178,c_426])).

cnf(c_6143,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(sK1,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_6142,c_2442])).

cnf(c_6176,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_6143,c_12])).

cnf(c_4421,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_359,c_4377])).

cnf(c_6179,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6176,c_3489,c_4421])).

cnf(c_169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_580,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44082,c_6179,c_580,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.05/2.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/2.06  
% 11.05/2.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.05/2.06  
% 11.05/2.06  ------  iProver source info
% 11.05/2.06  
% 11.05/2.06  git: date: 2020-06-30 10:37:57 +0100
% 11.05/2.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.05/2.06  git: non_committed_changes: false
% 11.05/2.06  git: last_make_outside_of_git: false
% 11.05/2.06  
% 11.05/2.06  ------ 
% 11.05/2.06  
% 11.05/2.06  ------ Input Options
% 11.05/2.06  
% 11.05/2.06  --out_options                           all
% 11.05/2.06  --tptp_safe_out                         true
% 11.05/2.06  --problem_path                          ""
% 11.05/2.06  --include_path                          ""
% 11.05/2.06  --clausifier                            res/vclausify_rel
% 11.05/2.06  --clausifier_options                    ""
% 11.05/2.06  --stdin                                 false
% 11.05/2.06  --stats_out                             all
% 11.05/2.06  
% 11.05/2.06  ------ General Options
% 11.05/2.06  
% 11.05/2.06  --fof                                   false
% 11.05/2.06  --time_out_real                         305.
% 11.05/2.06  --time_out_virtual                      -1.
% 11.05/2.06  --symbol_type_check                     false
% 11.05/2.06  --clausify_out                          false
% 11.05/2.06  --sig_cnt_out                           false
% 11.73/2.06  --trig_cnt_out                          false
% 11.73/2.06  --trig_cnt_out_tolerance                1.
% 11.73/2.06  --trig_cnt_out_sk_spl                   false
% 11.73/2.06  --abstr_cl_out                          false
% 11.73/2.06  
% 11.73/2.06  ------ Global Options
% 11.73/2.06  
% 11.73/2.06  --schedule                              default
% 11.73/2.06  --add_important_lit                     false
% 11.73/2.06  --prop_solver_per_cl                    1000
% 11.73/2.06  --min_unsat_core                        false
% 11.73/2.06  --soft_assumptions                      false
% 11.73/2.06  --soft_lemma_size                       3
% 11.73/2.06  --prop_impl_unit_size                   0
% 11.73/2.06  --prop_impl_unit                        []
% 11.73/2.06  --share_sel_clauses                     true
% 11.73/2.06  --reset_solvers                         false
% 11.73/2.06  --bc_imp_inh                            [conj_cone]
% 11.73/2.06  --conj_cone_tolerance                   3.
% 11.73/2.06  --extra_neg_conj                        none
% 11.73/2.06  --large_theory_mode                     true
% 11.73/2.06  --prolific_symb_bound                   200
% 11.73/2.06  --lt_threshold                          2000
% 11.73/2.06  --clause_weak_htbl                      true
% 11.73/2.06  --gc_record_bc_elim                     false
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing Options
% 11.73/2.06  
% 11.73/2.06  --preprocessing_flag                    true
% 11.73/2.06  --time_out_prep_mult                    0.1
% 11.73/2.06  --splitting_mode                        input
% 11.73/2.06  --splitting_grd                         true
% 11.73/2.06  --splitting_cvd                         false
% 11.73/2.06  --splitting_cvd_svl                     false
% 11.73/2.06  --splitting_nvd                         32
% 11.73/2.06  --sub_typing                            true
% 11.73/2.06  --prep_gs_sim                           true
% 11.73/2.06  --prep_unflatten                        true
% 11.73/2.06  --prep_res_sim                          true
% 11.73/2.06  --prep_upred                            true
% 11.73/2.06  --prep_sem_filter                       exhaustive
% 11.73/2.06  --prep_sem_filter_out                   false
% 11.73/2.06  --pred_elim                             true
% 11.73/2.06  --res_sim_input                         true
% 11.73/2.06  --eq_ax_congr_red                       true
% 11.73/2.06  --pure_diseq_elim                       true
% 11.73/2.06  --brand_transform                       false
% 11.73/2.06  --non_eq_to_eq                          false
% 11.73/2.06  --prep_def_merge                        true
% 11.73/2.06  --prep_def_merge_prop_impl              false
% 11.73/2.06  --prep_def_merge_mbd                    true
% 11.73/2.06  --prep_def_merge_tr_red                 false
% 11.73/2.06  --prep_def_merge_tr_cl                  false
% 11.73/2.06  --smt_preprocessing                     true
% 11.73/2.06  --smt_ac_axioms                         fast
% 11.73/2.06  --preprocessed_out                      false
% 11.73/2.06  --preprocessed_stats                    false
% 11.73/2.06  
% 11.73/2.06  ------ Abstraction refinement Options
% 11.73/2.06  
% 11.73/2.06  --abstr_ref                             []
% 11.73/2.06  --abstr_ref_prep                        false
% 11.73/2.06  --abstr_ref_until_sat                   false
% 11.73/2.06  --abstr_ref_sig_restrict                funpre
% 11.73/2.06  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/2.06  --abstr_ref_under                       []
% 11.73/2.06  
% 11.73/2.06  ------ SAT Options
% 11.73/2.06  
% 11.73/2.06  --sat_mode                              false
% 11.73/2.06  --sat_fm_restart_options                ""
% 11.73/2.06  --sat_gr_def                            false
% 11.73/2.06  --sat_epr_types                         true
% 11.73/2.06  --sat_non_cyclic_types                  false
% 11.73/2.06  --sat_finite_models                     false
% 11.73/2.06  --sat_fm_lemmas                         false
% 11.73/2.06  --sat_fm_prep                           false
% 11.73/2.06  --sat_fm_uc_incr                        true
% 11.73/2.06  --sat_out_model                         small
% 11.73/2.06  --sat_out_clauses                       false
% 11.73/2.06  
% 11.73/2.06  ------ QBF Options
% 11.73/2.06  
% 11.73/2.06  --qbf_mode                              false
% 11.73/2.06  --qbf_elim_univ                         false
% 11.73/2.06  --qbf_dom_inst                          none
% 11.73/2.06  --qbf_dom_pre_inst                      false
% 11.73/2.06  --qbf_sk_in                             false
% 11.73/2.06  --qbf_pred_elim                         true
% 11.73/2.06  --qbf_split                             512
% 11.73/2.06  
% 11.73/2.06  ------ BMC1 Options
% 11.73/2.06  
% 11.73/2.06  --bmc1_incremental                      false
% 11.73/2.06  --bmc1_axioms                           reachable_all
% 11.73/2.06  --bmc1_min_bound                        0
% 11.73/2.06  --bmc1_max_bound                        -1
% 11.73/2.06  --bmc1_max_bound_default                -1
% 11.73/2.06  --bmc1_symbol_reachability              true
% 11.73/2.06  --bmc1_property_lemmas                  false
% 11.73/2.06  --bmc1_k_induction                      false
% 11.73/2.06  --bmc1_non_equiv_states                 false
% 11.73/2.06  --bmc1_deadlock                         false
% 11.73/2.06  --bmc1_ucm                              false
% 11.73/2.06  --bmc1_add_unsat_core                   none
% 11.73/2.06  --bmc1_unsat_core_children              false
% 11.73/2.06  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/2.06  --bmc1_out_stat                         full
% 11.73/2.06  --bmc1_ground_init                      false
% 11.73/2.06  --bmc1_pre_inst_next_state              false
% 11.73/2.06  --bmc1_pre_inst_state                   false
% 11.73/2.06  --bmc1_pre_inst_reach_state             false
% 11.73/2.06  --bmc1_out_unsat_core                   false
% 11.73/2.06  --bmc1_aig_witness_out                  false
% 11.73/2.06  --bmc1_verbose                          false
% 11.73/2.06  --bmc1_dump_clauses_tptp                false
% 11.73/2.06  --bmc1_dump_unsat_core_tptp             false
% 11.73/2.06  --bmc1_dump_file                        -
% 11.73/2.06  --bmc1_ucm_expand_uc_limit              128
% 11.73/2.06  --bmc1_ucm_n_expand_iterations          6
% 11.73/2.06  --bmc1_ucm_extend_mode                  1
% 11.73/2.06  --bmc1_ucm_init_mode                    2
% 11.73/2.06  --bmc1_ucm_cone_mode                    none
% 11.73/2.06  --bmc1_ucm_reduced_relation_type        0
% 11.73/2.06  --bmc1_ucm_relax_model                  4
% 11.73/2.06  --bmc1_ucm_full_tr_after_sat            true
% 11.73/2.06  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/2.06  --bmc1_ucm_layered_model                none
% 11.73/2.06  --bmc1_ucm_max_lemma_size               10
% 11.73/2.06  
% 11.73/2.06  ------ AIG Options
% 11.73/2.06  
% 11.73/2.06  --aig_mode                              false
% 11.73/2.06  
% 11.73/2.06  ------ Instantiation Options
% 11.73/2.06  
% 11.73/2.06  --instantiation_flag                    true
% 11.73/2.06  --inst_sos_flag                         true
% 11.73/2.06  --inst_sos_phase                        true
% 11.73/2.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/2.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/2.06  --inst_lit_sel_side                     num_symb
% 11.73/2.06  --inst_solver_per_active                1400
% 11.73/2.06  --inst_solver_calls_frac                1.
% 11.73/2.06  --inst_passive_queue_type               priority_queues
% 11.73/2.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/2.06  --inst_passive_queues_freq              [25;2]
% 11.73/2.06  --inst_dismatching                      true
% 11.73/2.06  --inst_eager_unprocessed_to_passive     true
% 11.73/2.06  --inst_prop_sim_given                   true
% 11.73/2.06  --inst_prop_sim_new                     false
% 11.73/2.06  --inst_subs_new                         false
% 11.73/2.06  --inst_eq_res_simp                      false
% 11.73/2.06  --inst_subs_given                       false
% 11.73/2.06  --inst_orphan_elimination               true
% 11.73/2.06  --inst_learning_loop_flag               true
% 11.73/2.06  --inst_learning_start                   3000
% 11.73/2.06  --inst_learning_factor                  2
% 11.73/2.06  --inst_start_prop_sim_after_learn       3
% 11.73/2.06  --inst_sel_renew                        solver
% 11.73/2.06  --inst_lit_activity_flag                true
% 11.73/2.06  --inst_restr_to_given                   false
% 11.73/2.06  --inst_activity_threshold               500
% 11.73/2.06  --inst_out_proof                        true
% 11.73/2.06  
% 11.73/2.06  ------ Resolution Options
% 11.73/2.06  
% 11.73/2.06  --resolution_flag                       true
% 11.73/2.06  --res_lit_sel                           adaptive
% 11.73/2.06  --res_lit_sel_side                      none
% 11.73/2.06  --res_ordering                          kbo
% 11.73/2.06  --res_to_prop_solver                    active
% 11.73/2.06  --res_prop_simpl_new                    false
% 11.73/2.06  --res_prop_simpl_given                  true
% 11.73/2.06  --res_passive_queue_type                priority_queues
% 11.73/2.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/2.06  --res_passive_queues_freq               [15;5]
% 11.73/2.06  --res_forward_subs                      full
% 11.73/2.06  --res_backward_subs                     full
% 11.73/2.06  --res_forward_subs_resolution           true
% 11.73/2.06  --res_backward_subs_resolution          true
% 11.73/2.06  --res_orphan_elimination                true
% 11.73/2.06  --res_time_limit                        2.
% 11.73/2.06  --res_out_proof                         true
% 11.73/2.06  
% 11.73/2.06  ------ Superposition Options
% 11.73/2.06  
% 11.73/2.06  --superposition_flag                    true
% 11.73/2.06  --sup_passive_queue_type                priority_queues
% 11.73/2.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/2.06  --sup_passive_queues_freq               [8;1;4]
% 11.73/2.06  --demod_completeness_check              fast
% 11.73/2.06  --demod_use_ground                      true
% 11.73/2.06  --sup_to_prop_solver                    passive
% 11.73/2.06  --sup_prop_simpl_new                    true
% 11.73/2.06  --sup_prop_simpl_given                  true
% 11.73/2.06  --sup_fun_splitting                     true
% 11.73/2.06  --sup_smt_interval                      50000
% 11.73/2.06  
% 11.73/2.06  ------ Superposition Simplification Setup
% 11.73/2.06  
% 11.73/2.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/2.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/2.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/2.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/2.06  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/2.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/2.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/2.06  --sup_immed_triv                        [TrivRules]
% 11.73/2.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_immed_bw_main                     []
% 11.73/2.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/2.06  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/2.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_input_bw                          []
% 11.73/2.06  
% 11.73/2.06  ------ Combination Options
% 11.73/2.06  
% 11.73/2.06  --comb_res_mult                         3
% 11.73/2.06  --comb_sup_mult                         2
% 11.73/2.06  --comb_inst_mult                        10
% 11.73/2.06  
% 11.73/2.06  ------ Debug Options
% 11.73/2.06  
% 11.73/2.06  --dbg_backtrace                         false
% 11.73/2.06  --dbg_dump_prop_clauses                 false
% 11.73/2.06  --dbg_dump_prop_clauses_file            -
% 11.73/2.06  --dbg_out_stat                          false
% 11.73/2.06  ------ Parsing...
% 11.73/2.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.73/2.06  ------ Proving...
% 11.73/2.06  ------ Problem Properties 
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  clauses                                 17
% 11.73/2.06  conjectures                             2
% 11.73/2.06  EPR                                     1
% 11.73/2.06  Horn                                    17
% 11.73/2.06  unary                                   16
% 11.73/2.06  binary                                  1
% 11.73/2.06  lits                                    18
% 11.73/2.06  lits eq                                 18
% 11.73/2.06  fd_pure                                 0
% 11.73/2.06  fd_pseudo                               0
% 11.73/2.06  fd_cond                                 0
% 11.73/2.06  fd_pseudo_cond                          0
% 11.73/2.06  AC symbols                              1
% 11.73/2.06  
% 11.73/2.06  ------ Schedule dynamic 5 is on 
% 11.73/2.06  
% 11.73/2.06  ------ pure equality problem: resolution off 
% 11.73/2.06  
% 11.73/2.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  ------ 
% 11.73/2.06  Current options:
% 11.73/2.06  ------ 
% 11.73/2.06  
% 11.73/2.06  ------ Input Options
% 11.73/2.06  
% 11.73/2.06  --out_options                           all
% 11.73/2.06  --tptp_safe_out                         true
% 11.73/2.06  --problem_path                          ""
% 11.73/2.06  --include_path                          ""
% 11.73/2.06  --clausifier                            res/vclausify_rel
% 11.73/2.06  --clausifier_options                    ""
% 11.73/2.06  --stdin                                 false
% 11.73/2.06  --stats_out                             all
% 11.73/2.06  
% 11.73/2.06  ------ General Options
% 11.73/2.06  
% 11.73/2.06  --fof                                   false
% 11.73/2.06  --time_out_real                         305.
% 11.73/2.06  --time_out_virtual                      -1.
% 11.73/2.06  --symbol_type_check                     false
% 11.73/2.06  --clausify_out                          false
% 11.73/2.06  --sig_cnt_out                           false
% 11.73/2.06  --trig_cnt_out                          false
% 11.73/2.06  --trig_cnt_out_tolerance                1.
% 11.73/2.06  --trig_cnt_out_sk_spl                   false
% 11.73/2.06  --abstr_cl_out                          false
% 11.73/2.06  
% 11.73/2.06  ------ Global Options
% 11.73/2.06  
% 11.73/2.06  --schedule                              default
% 11.73/2.06  --add_important_lit                     false
% 11.73/2.06  --prop_solver_per_cl                    1000
% 11.73/2.06  --min_unsat_core                        false
% 11.73/2.06  --soft_assumptions                      false
% 11.73/2.06  --soft_lemma_size                       3
% 11.73/2.06  --prop_impl_unit_size                   0
% 11.73/2.06  --prop_impl_unit                        []
% 11.73/2.06  --share_sel_clauses                     true
% 11.73/2.06  --reset_solvers                         false
% 11.73/2.06  --bc_imp_inh                            [conj_cone]
% 11.73/2.06  --conj_cone_tolerance                   3.
% 11.73/2.06  --extra_neg_conj                        none
% 11.73/2.06  --large_theory_mode                     true
% 11.73/2.06  --prolific_symb_bound                   200
% 11.73/2.06  --lt_threshold                          2000
% 11.73/2.06  --clause_weak_htbl                      true
% 11.73/2.06  --gc_record_bc_elim                     false
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing Options
% 11.73/2.06  
% 11.73/2.06  --preprocessing_flag                    true
% 11.73/2.06  --time_out_prep_mult                    0.1
% 11.73/2.06  --splitting_mode                        input
% 11.73/2.06  --splitting_grd                         true
% 11.73/2.06  --splitting_cvd                         false
% 11.73/2.06  --splitting_cvd_svl                     false
% 11.73/2.06  --splitting_nvd                         32
% 11.73/2.06  --sub_typing                            true
% 11.73/2.06  --prep_gs_sim                           true
% 11.73/2.06  --prep_unflatten                        true
% 11.73/2.06  --prep_res_sim                          true
% 11.73/2.06  --prep_upred                            true
% 11.73/2.06  --prep_sem_filter                       exhaustive
% 11.73/2.06  --prep_sem_filter_out                   false
% 11.73/2.06  --pred_elim                             true
% 11.73/2.06  --res_sim_input                         true
% 11.73/2.06  --eq_ax_congr_red                       true
% 11.73/2.06  --pure_diseq_elim                       true
% 11.73/2.06  --brand_transform                       false
% 11.73/2.06  --non_eq_to_eq                          false
% 11.73/2.06  --prep_def_merge                        true
% 11.73/2.06  --prep_def_merge_prop_impl              false
% 11.73/2.06  --prep_def_merge_mbd                    true
% 11.73/2.06  --prep_def_merge_tr_red                 false
% 11.73/2.06  --prep_def_merge_tr_cl                  false
% 11.73/2.06  --smt_preprocessing                     true
% 11.73/2.06  --smt_ac_axioms                         fast
% 11.73/2.06  --preprocessed_out                      false
% 11.73/2.06  --preprocessed_stats                    false
% 11.73/2.06  
% 11.73/2.06  ------ Abstraction refinement Options
% 11.73/2.06  
% 11.73/2.06  --abstr_ref                             []
% 11.73/2.06  --abstr_ref_prep                        false
% 11.73/2.06  --abstr_ref_until_sat                   false
% 11.73/2.06  --abstr_ref_sig_restrict                funpre
% 11.73/2.06  --abstr_ref_af_restrict_to_split_sk     false
% 11.73/2.06  --abstr_ref_under                       []
% 11.73/2.06  
% 11.73/2.06  ------ SAT Options
% 11.73/2.06  
% 11.73/2.06  --sat_mode                              false
% 11.73/2.06  --sat_fm_restart_options                ""
% 11.73/2.06  --sat_gr_def                            false
% 11.73/2.06  --sat_epr_types                         true
% 11.73/2.06  --sat_non_cyclic_types                  false
% 11.73/2.06  --sat_finite_models                     false
% 11.73/2.06  --sat_fm_lemmas                         false
% 11.73/2.06  --sat_fm_prep                           false
% 11.73/2.06  --sat_fm_uc_incr                        true
% 11.73/2.06  --sat_out_model                         small
% 11.73/2.06  --sat_out_clauses                       false
% 11.73/2.06  
% 11.73/2.06  ------ QBF Options
% 11.73/2.06  
% 11.73/2.06  --qbf_mode                              false
% 11.73/2.06  --qbf_elim_univ                         false
% 11.73/2.06  --qbf_dom_inst                          none
% 11.73/2.06  --qbf_dom_pre_inst                      false
% 11.73/2.06  --qbf_sk_in                             false
% 11.73/2.06  --qbf_pred_elim                         true
% 11.73/2.06  --qbf_split                             512
% 11.73/2.06  
% 11.73/2.06  ------ BMC1 Options
% 11.73/2.06  
% 11.73/2.06  --bmc1_incremental                      false
% 11.73/2.06  --bmc1_axioms                           reachable_all
% 11.73/2.06  --bmc1_min_bound                        0
% 11.73/2.06  --bmc1_max_bound                        -1
% 11.73/2.06  --bmc1_max_bound_default                -1
% 11.73/2.06  --bmc1_symbol_reachability              true
% 11.73/2.06  --bmc1_property_lemmas                  false
% 11.73/2.06  --bmc1_k_induction                      false
% 11.73/2.06  --bmc1_non_equiv_states                 false
% 11.73/2.06  --bmc1_deadlock                         false
% 11.73/2.06  --bmc1_ucm                              false
% 11.73/2.06  --bmc1_add_unsat_core                   none
% 11.73/2.06  --bmc1_unsat_core_children              false
% 11.73/2.06  --bmc1_unsat_core_extrapolate_axioms    false
% 11.73/2.06  --bmc1_out_stat                         full
% 11.73/2.06  --bmc1_ground_init                      false
% 11.73/2.06  --bmc1_pre_inst_next_state              false
% 11.73/2.06  --bmc1_pre_inst_state                   false
% 11.73/2.06  --bmc1_pre_inst_reach_state             false
% 11.73/2.06  --bmc1_out_unsat_core                   false
% 11.73/2.06  --bmc1_aig_witness_out                  false
% 11.73/2.06  --bmc1_verbose                          false
% 11.73/2.06  --bmc1_dump_clauses_tptp                false
% 11.73/2.06  --bmc1_dump_unsat_core_tptp             false
% 11.73/2.06  --bmc1_dump_file                        -
% 11.73/2.06  --bmc1_ucm_expand_uc_limit              128
% 11.73/2.06  --bmc1_ucm_n_expand_iterations          6
% 11.73/2.06  --bmc1_ucm_extend_mode                  1
% 11.73/2.06  --bmc1_ucm_init_mode                    2
% 11.73/2.06  --bmc1_ucm_cone_mode                    none
% 11.73/2.06  --bmc1_ucm_reduced_relation_type        0
% 11.73/2.06  --bmc1_ucm_relax_model                  4
% 11.73/2.06  --bmc1_ucm_full_tr_after_sat            true
% 11.73/2.06  --bmc1_ucm_expand_neg_assumptions       false
% 11.73/2.06  --bmc1_ucm_layered_model                none
% 11.73/2.06  --bmc1_ucm_max_lemma_size               10
% 11.73/2.06  
% 11.73/2.06  ------ AIG Options
% 11.73/2.06  
% 11.73/2.06  --aig_mode                              false
% 11.73/2.06  
% 11.73/2.06  ------ Instantiation Options
% 11.73/2.06  
% 11.73/2.06  --instantiation_flag                    true
% 11.73/2.06  --inst_sos_flag                         true
% 11.73/2.06  --inst_sos_phase                        true
% 11.73/2.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.73/2.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.73/2.06  --inst_lit_sel_side                     none
% 11.73/2.06  --inst_solver_per_active                1400
% 11.73/2.06  --inst_solver_calls_frac                1.
% 11.73/2.06  --inst_passive_queue_type               priority_queues
% 11.73/2.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.73/2.06  --inst_passive_queues_freq              [25;2]
% 11.73/2.06  --inst_dismatching                      true
% 11.73/2.06  --inst_eager_unprocessed_to_passive     true
% 11.73/2.06  --inst_prop_sim_given                   true
% 11.73/2.06  --inst_prop_sim_new                     false
% 11.73/2.06  --inst_subs_new                         false
% 11.73/2.06  --inst_eq_res_simp                      false
% 11.73/2.06  --inst_subs_given                       false
% 11.73/2.06  --inst_orphan_elimination               true
% 11.73/2.06  --inst_learning_loop_flag               true
% 11.73/2.06  --inst_learning_start                   3000
% 11.73/2.06  --inst_learning_factor                  2
% 11.73/2.06  --inst_start_prop_sim_after_learn       3
% 11.73/2.06  --inst_sel_renew                        solver
% 11.73/2.06  --inst_lit_activity_flag                true
% 11.73/2.06  --inst_restr_to_given                   false
% 11.73/2.06  --inst_activity_threshold               500
% 11.73/2.06  --inst_out_proof                        true
% 11.73/2.06  
% 11.73/2.06  ------ Resolution Options
% 11.73/2.06  
% 11.73/2.06  --resolution_flag                       false
% 11.73/2.06  --res_lit_sel                           adaptive
% 11.73/2.06  --res_lit_sel_side                      none
% 11.73/2.06  --res_ordering                          kbo
% 11.73/2.06  --res_to_prop_solver                    active
% 11.73/2.06  --res_prop_simpl_new                    false
% 11.73/2.06  --res_prop_simpl_given                  true
% 11.73/2.06  --res_passive_queue_type                priority_queues
% 11.73/2.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.73/2.06  --res_passive_queues_freq               [15;5]
% 11.73/2.06  --res_forward_subs                      full
% 11.73/2.06  --res_backward_subs                     full
% 11.73/2.06  --res_forward_subs_resolution           true
% 11.73/2.06  --res_backward_subs_resolution          true
% 11.73/2.06  --res_orphan_elimination                true
% 11.73/2.06  --res_time_limit                        2.
% 11.73/2.06  --res_out_proof                         true
% 11.73/2.06  
% 11.73/2.06  ------ Superposition Options
% 11.73/2.06  
% 11.73/2.06  --superposition_flag                    true
% 11.73/2.06  --sup_passive_queue_type                priority_queues
% 11.73/2.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.73/2.06  --sup_passive_queues_freq               [8;1;4]
% 11.73/2.06  --demod_completeness_check              fast
% 11.73/2.06  --demod_use_ground                      true
% 11.73/2.06  --sup_to_prop_solver                    passive
% 11.73/2.06  --sup_prop_simpl_new                    true
% 11.73/2.06  --sup_prop_simpl_given                  true
% 11.73/2.06  --sup_fun_splitting                     true
% 11.73/2.06  --sup_smt_interval                      50000
% 11.73/2.06  
% 11.73/2.06  ------ Superposition Simplification Setup
% 11.73/2.06  
% 11.73/2.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.73/2.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.73/2.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.73/2.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.73/2.06  --sup_full_triv                         [TrivRules;PropSubs]
% 11.73/2.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.73/2.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.73/2.06  --sup_immed_triv                        [TrivRules]
% 11.73/2.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_immed_bw_main                     []
% 11.73/2.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.73/2.06  --sup_input_triv                        [Unflattening;TrivRules]
% 11.73/2.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.73/2.06  --sup_input_bw                          []
% 11.73/2.06  
% 11.73/2.06  ------ Combination Options
% 11.73/2.06  
% 11.73/2.06  --comb_res_mult                         3
% 11.73/2.06  --comb_sup_mult                         2
% 11.73/2.06  --comb_inst_mult                        10
% 11.73/2.06  
% 11.73/2.06  ------ Debug Options
% 11.73/2.06  
% 11.73/2.06  --dbg_backtrace                         false
% 11.73/2.06  --dbg_dump_prop_clauses                 false
% 11.73/2.06  --dbg_dump_prop_clauses_file            -
% 11.73/2.06  --dbg_out_stat                          false
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  ------ Proving...
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  % SZS status Theorem for theBenchmark.p
% 11.73/2.06  
% 11.73/2.06  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/2.06  
% 11.73/2.06  fof(f16,conjecture,(
% 11.73/2.06    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f17,negated_conjecture,(
% 11.73/2.06    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 11.73/2.06    inference(negated_conjecture,[],[f16])).
% 11.73/2.06  
% 11.73/2.06  fof(f22,plain,(
% 11.73/2.06    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 11.73/2.06    inference(ennf_transformation,[],[f17])).
% 11.73/2.06  
% 11.73/2.06  fof(f23,plain,(
% 11.73/2.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 11.73/2.06    inference(flattening,[],[f22])).
% 11.73/2.06  
% 11.73/2.06  fof(f25,plain,(
% 11.73/2.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 11.73/2.06    introduced(choice_axiom,[])).
% 11.73/2.06  
% 11.73/2.06  fof(f26,plain,(
% 11.73/2.06    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 11.73/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).
% 11.73/2.06  
% 11.73/2.06  fof(f43,plain,(
% 11.73/2.06    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 11.73/2.06    inference(cnf_transformation,[],[f26])).
% 11.73/2.06  
% 11.73/2.06  fof(f15,axiom,(
% 11.73/2.06    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f42,plain,(
% 11.73/2.06    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f15])).
% 11.73/2.06  
% 11.73/2.06  fof(f1,axiom,(
% 11.73/2.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f27,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f1])).
% 11.73/2.06  
% 11.73/2.06  fof(f12,axiom,(
% 11.73/2.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f39,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f12])).
% 11.73/2.06  
% 11.73/2.06  fof(f10,axiom,(
% 11.73/2.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f37,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.73/2.06    inference(cnf_transformation,[],[f10])).
% 11.73/2.06  
% 11.73/2.06  fof(f13,axiom,(
% 11.73/2.06    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f40,plain,(
% 11.73/2.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f13])).
% 11.73/2.06  
% 11.73/2.06  fof(f8,axiom,(
% 11.73/2.06    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f35,plain,(
% 11.73/2.06    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.73/2.06    inference(cnf_transformation,[],[f8])).
% 11.73/2.06  
% 11.73/2.06  fof(f14,axiom,(
% 11.73/2.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f41,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.73/2.06    inference(cnf_transformation,[],[f14])).
% 11.73/2.06  
% 11.73/2.06  fof(f49,plain,(
% 11.73/2.06    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.73/2.06    inference(definition_unfolding,[],[f35,f41])).
% 11.73/2.06  
% 11.73/2.06  fof(f11,axiom,(
% 11.73/2.06    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f38,plain,(
% 11.73/2.06    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.73/2.06    inference(cnf_transformation,[],[f11])).
% 11.73/2.06  
% 11.73/2.06  fof(f5,axiom,(
% 11.73/2.06    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f24,plain,(
% 11.73/2.06    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 11.73/2.06    inference(nnf_transformation,[],[f5])).
% 11.73/2.06  
% 11.73/2.06  fof(f31,plain,(
% 11.73/2.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f24])).
% 11.73/2.06  
% 11.73/2.06  fof(f6,axiom,(
% 11.73/2.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f21,plain,(
% 11.73/2.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.73/2.06    inference(ennf_transformation,[],[f6])).
% 11.73/2.06  
% 11.73/2.06  fof(f33,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f21])).
% 11.73/2.06  
% 11.73/2.06  fof(f3,axiom,(
% 11.73/2.06    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f19,plain,(
% 11.73/2.06    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.73/2.06    inference(unused_predicate_definition_removal,[],[f3])).
% 11.73/2.06  
% 11.73/2.06  fof(f20,plain,(
% 11.73/2.06    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 11.73/2.06    inference(ennf_transformation,[],[f19])).
% 11.73/2.06  
% 11.73/2.06  fof(f29,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f20])).
% 11.73/2.06  
% 11.73/2.06  fof(f48,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.73/2.06    inference(definition_unfolding,[],[f29,f41])).
% 11.73/2.06  
% 11.73/2.06  fof(f45,plain,(
% 11.73/2.06    r1_xboole_0(sK3,sK1)),
% 11.73/2.06    inference(cnf_transformation,[],[f26])).
% 11.73/2.06  
% 11.73/2.06  fof(f9,axiom,(
% 11.73/2.06    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f36,plain,(
% 11.73/2.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f9])).
% 11.73/2.06  
% 11.73/2.06  fof(f7,axiom,(
% 11.73/2.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f34,plain,(
% 11.73/2.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.73/2.06    inference(cnf_transformation,[],[f7])).
% 11.73/2.06  
% 11.73/2.06  fof(f44,plain,(
% 11.73/2.06    r1_xboole_0(sK2,sK0)),
% 11.73/2.06    inference(cnf_transformation,[],[f26])).
% 11.73/2.06  
% 11.73/2.06  fof(f2,axiom,(
% 11.73/2.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.73/2.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.06  
% 11.73/2.06  fof(f28,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.73/2.06    inference(cnf_transformation,[],[f2])).
% 11.73/2.06  
% 11.73/2.06  fof(f47,plain,(
% 11.73/2.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.73/2.06    inference(definition_unfolding,[],[f28,f41,f41])).
% 11.73/2.06  
% 11.73/2.06  fof(f46,plain,(
% 11.73/2.06    sK1 != sK2),
% 11.73/2.06    inference(cnf_transformation,[],[f26])).
% 11.73/2.06  
% 11.73/2.06  cnf(c_170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_181,plain,
% 11.73/2.06      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 11.73/2.06      inference(instantiation,[status(thm)],[c_170]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_44082,plain,
% 11.73/2.06      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 11.73/2.06      inference(instantiation,[status(thm)],[c_181]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_18,negated_conjecture,
% 11.73/2.06      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 11.73/2.06      inference(cnf_transformation,[],[f43]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_14,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.73/2.06      inference(cnf_transformation,[],[f42]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_0,plain,
% 11.73/2.06      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.73/2.06      inference(cnf_transformation,[],[f27]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_168,negated_conjecture,
% 11.73/2.06      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 11.73/2.06      inference(theory_normalisation,[status(thm)],[c_18,c_14,c_0]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_178,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2415,plain,
% 11.73/2.06      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_168,c_178]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_12,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.73/2.06      inference(cnf_transformation,[],[f39]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_426,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2734,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2415,c_426]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2720,plain,
% 11.73/2.06      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_2415]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_3911,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2720,c_426]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_10,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.73/2.06      inference(cnf_transformation,[],[f37]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_431,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_434,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_431,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_853,plain,
% 11.73/2.06      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_168,c_14]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1115,plain,
% 11.73/2.06      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_853,c_14]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1950,plain,
% 11.73/2.06      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK2,sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_434,c_1115]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1955,plain,
% 11.73/2.06      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_1950,c_168]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2159,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_1955,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5195,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) = k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2159,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2160,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_1955,c_434]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_13,plain,
% 11.73/2.06      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.73/2.06      inference(cnf_transformation,[],[f40]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_8,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.73/2.06      inference(cnf_transformation,[],[f49]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_11,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.73/2.06      inference(cnf_transformation,[],[f38]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_176,plain,
% 11.73/2.06      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_8,c_11]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_823,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_13,c_176]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_824,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_823,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2161,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_1955,c_824]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5,plain,
% 11.73/2.06      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.73/2.06      inference(cnf_transformation,[],[f31]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_71,plain,
% 11.73/2.06      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.73/2.06      inference(prop_impl,[status(thm)],[c_5]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6,plain,
% 11.73/2.06      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.73/2.06      inference(cnf_transformation,[],[f33]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_139,plain,
% 11.73/2.06      ( k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1 ),
% 11.73/2.06      inference(resolution,[status(thm)],[c_71,c_6]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2376,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2161,c_139]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5442,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_2160,c_2376]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5454,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_5442,c_14]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5476,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK0),sK0) ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_5195,c_5454]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5186,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_2159]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2154,plain,
% 11.73/2.06      ( k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_1955]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2333,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2154,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2768,plain,
% 11.73/2.06      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK0)) = k2_xboole_0(sK0,sK1) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2415,c_434]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2963,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK2,sK0),k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2768,c_434]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2418,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_434,c_178]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2973,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK2,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_2963,c_1955,c_2418]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_3070,plain,
% 11.73/2.06      ( k2_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2973,c_14]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2,plain,
% 11.73/2.06      ( ~ r1_xboole_0(X0,X1)
% 11.73/2.06      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.73/2.06      inference(cnf_transformation,[],[f48]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_16,negated_conjecture,
% 11.73/2.06      ( r1_xboole_0(sK3,sK1) ),
% 11.73/2.06      inference(cnf_transformation,[],[f45]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_127,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.73/2.06      | sK3 != X0
% 11.73/2.06      | sK1 != X1 ),
% 11.73/2.06      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_128,plain,
% 11.73/2.06      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 11.73/2.06      inference(unflattening,[status(thm)],[c_127]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_355,plain,
% 11.73/2.06      ( k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(sK3,sK1) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_128,c_139]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_9,plain,
% 11.73/2.06      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.73/2.06      inference(cnf_transformation,[],[f36]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_147,plain,
% 11.73/2.06      ( X0 != X1 | k4_xboole_0(X0,X2) != X3 | k2_xboole_0(X3,X1) = X1 ),
% 11.73/2.06      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_148,plain,
% 11.73/2.06      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.73/2.06      inference(unflattening,[status(thm)],[c_147]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_167,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.73/2.06      inference(theory_normalisation,[status(thm)],[c_148,c_14,c_0]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_359,plain,
% 11.73/2.06      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_355,c_167]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_809,plain,
% 11.73/2.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_359,c_13]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_951,plain,
% 11.73/2.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_168,c_824]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2621,plain,
% 11.73/2.06      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_809,c_951]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2846,plain,
% 11.73/2.06      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2621,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_7,plain,
% 11.73/2.06      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.73/2.06      inference(cnf_transformation,[],[f34]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2848,plain,
% 11.73/2.06      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_2846,c_7]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_3072,plain,
% 11.73/2.06      ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,sK0) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_3070,c_2848]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5204,plain,
% 11.73/2.06      ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_5186,c_2333,c_3072]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_945,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_824]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5205,plain,
% 11.73/2.06      ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_5204,c_945]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5477,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK0) = k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_5476,c_5205]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1620,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_945,c_10]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1623,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_1620,c_7]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4636,plain,
% 11.73/2.06      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_0,c_1623]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5478,plain,
% 11.73/2.06      ( k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,sK1) ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_5477,c_7,c_4636]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_5980,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_5478,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_17,negated_conjecture,
% 11.73/2.06      ( r1_xboole_0(sK2,sK0) ),
% 11.73/2.06      inference(cnf_transformation,[],[f44]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_132,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.73/2.06      | sK0 != X1
% 11.73/2.06      | sK2 != X0 ),
% 11.73/2.06      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_133,plain,
% 11.73/2.06      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 11.73/2.06      inference(unflattening,[status(thm)],[c_132]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_356,plain,
% 11.73/2.06      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_133,c_139]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_358,plain,
% 11.73/2.06      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_356,c_167]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(cnf_transformation,[],[f47]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1751,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_426,c_1]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_428,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_10,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1755,plain,
% 11.73/2.06      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.73/2.06      inference(light_normalisation,
% 11.73/2.06                [status(thm)],
% 11.73/2.06                [c_1751,c_11,c_428,c_945]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_1773,plain,
% 11.73/2.06      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_358,c_1755]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4377,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_428,c_428,c_1755]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4415,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK2,sK0),sK3)) = sK3 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2768,c_4377]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_429,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_168,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4476,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = sK3 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_4415,c_429,c_3072]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_810,plain,
% 11.73/2.06      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_358,c_13]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_3487,plain,
% 11.73/2.06      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_2848,c_810]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_3489,plain,
% 11.73/2.06      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_3487,c_358]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4477,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = sK3 ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_4476,c_3489]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6000,plain,
% 11.73/2.06      ( sK0 = sK3 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_5980,c_1773,c_4477]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6142,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK3)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_2734,c_3911,c_6000]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_2442,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_178,c_426]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6143,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(sK1,X0),sK3) ),
% 11.73/2.06      inference(demodulation,[status(thm)],[c_6142,c_2442]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6176,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_6143,c_12]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_4421,plain,
% 11.73/2.06      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = sK1 ),
% 11.73/2.06      inference(superposition,[status(thm)],[c_359,c_4377]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_6179,plain,
% 11.73/2.06      ( sK2 = sK1 ),
% 11.73/2.06      inference(light_normalisation,[status(thm)],[c_6176,c_3489,c_4421]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_169,plain,( X0 = X0 ),theory(equality) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_580,plain,
% 11.73/2.06      ( sK1 = sK1 ),
% 11.73/2.06      inference(instantiation,[status(thm)],[c_169]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(c_15,negated_conjecture,
% 11.73/2.06      ( sK1 != sK2 ),
% 11.73/2.06      inference(cnf_transformation,[],[f46]) ).
% 11.73/2.06  
% 11.73/2.06  cnf(contradiction,plain,
% 11.73/2.06      ( $false ),
% 11.73/2.06      inference(minisat,[status(thm)],[c_44082,c_6179,c_580,c_15]) ).
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/2.06  
% 11.73/2.06  ------                               Statistics
% 11.73/2.06  
% 11.73/2.06  ------ General
% 11.73/2.06  
% 11.73/2.06  abstr_ref_over_cycles:                  0
% 11.73/2.06  abstr_ref_under_cycles:                 0
% 11.73/2.06  gc_basic_clause_elim:                   0
% 11.73/2.06  forced_gc_time:                         0
% 11.73/2.06  parsing_time:                           0.008
% 11.73/2.06  unif_index_cands_time:                  0.
% 11.73/2.06  unif_index_add_time:                    0.
% 11.73/2.06  orderings_time:                         0.
% 11.73/2.06  out_proof_time:                         0.009
% 11.73/2.06  total_time:                             1.383
% 11.73/2.06  num_of_symbols:                         44
% 11.73/2.06  num_of_terms:                           76100
% 11.73/2.06  
% 11.73/2.06  ------ Preprocessing
% 11.73/2.06  
% 11.73/2.06  num_of_splits:                          0
% 11.73/2.06  num_of_split_atoms:                     4
% 11.73/2.06  num_of_reused_defs:                     1
% 11.73/2.06  num_eq_ax_congr_red:                    1
% 11.73/2.06  num_of_sem_filtered_clauses:            0
% 11.73/2.06  num_of_subtypes:                        0
% 11.73/2.06  monotx_restored_types:                  0
% 11.73/2.06  sat_num_of_epr_types:                   0
% 11.73/2.06  sat_num_of_non_cyclic_types:            0
% 11.73/2.06  sat_guarded_non_collapsed_types:        0
% 11.73/2.06  num_pure_diseq_elim:                    0
% 11.73/2.06  simp_replaced_by:                       0
% 11.73/2.06  res_preprocessed:                       57
% 11.73/2.06  prep_upred:                             0
% 11.73/2.06  prep_unflattend:                        8
% 11.73/2.06  smt_new_axioms:                         0
% 11.73/2.06  pred_elim_cands:                        0
% 11.73/2.06  pred_elim:                              2
% 11.73/2.06  pred_elim_cl:                           2
% 11.73/2.06  pred_elim_cycles:                       3
% 11.73/2.06  merged_defs:                            2
% 11.73/2.06  merged_defs_ncl:                        0
% 11.73/2.06  bin_hyper_res:                          2
% 11.73/2.06  prep_cycles:                            3
% 11.73/2.06  pred_elim_time:                         0.001
% 11.73/2.06  splitting_time:                         0.
% 11.73/2.06  sem_filter_time:                        0.
% 11.73/2.06  monotx_time:                            0.
% 11.73/2.06  subtype_inf_time:                       0.
% 11.73/2.06  
% 11.73/2.06  ------ Problem properties
% 11.73/2.06  
% 11.73/2.06  clauses:                                17
% 11.73/2.06  conjectures:                            2
% 11.73/2.06  epr:                                    1
% 11.73/2.06  horn:                                   17
% 11.73/2.06  ground:                                 4
% 11.73/2.06  unary:                                  16
% 11.73/2.06  binary:                                 1
% 11.73/2.06  lits:                                   18
% 11.73/2.06  lits_eq:                                18
% 11.73/2.06  fd_pure:                                0
% 11.73/2.06  fd_pseudo:                              0
% 11.73/2.06  fd_cond:                                0
% 11.73/2.06  fd_pseudo_cond:                         0
% 11.73/2.06  ac_symbols:                             1
% 11.73/2.06  
% 11.73/2.06  ------ Propositional Solver
% 11.73/2.06  
% 11.73/2.06  prop_solver_calls:                      31
% 11.73/2.06  prop_fast_solver_calls:                 665
% 11.73/2.06  smt_solver_calls:                       0
% 11.73/2.06  smt_fast_solver_calls:                  0
% 11.73/2.06  prop_num_of_clauses:                    12734
% 11.73/2.06  prop_preprocess_simplified:             12785
% 11.73/2.06  prop_fo_subsumed:                       0
% 11.73/2.06  prop_solver_time:                       0.
% 11.73/2.06  smt_solver_time:                        0.
% 11.73/2.06  smt_fast_solver_time:                   0.
% 11.73/2.06  prop_fast_solver_time:                  0.
% 11.73/2.06  prop_unsat_core_time:                   0.001
% 11.73/2.06  
% 11.73/2.06  ------ QBF
% 11.73/2.06  
% 11.73/2.06  qbf_q_res:                              0
% 11.73/2.06  qbf_num_tautologies:                    0
% 11.73/2.06  qbf_prep_cycles:                        0
% 11.73/2.06  
% 11.73/2.06  ------ BMC1
% 11.73/2.06  
% 11.73/2.06  bmc1_current_bound:                     -1
% 11.73/2.06  bmc1_last_solved_bound:                 -1
% 11.73/2.06  bmc1_unsat_core_size:                   -1
% 11.73/2.06  bmc1_unsat_core_parents_size:           -1
% 11.73/2.06  bmc1_merge_next_fun:                    0
% 11.73/2.06  bmc1_unsat_core_clauses_time:           0.
% 11.73/2.06  
% 11.73/2.06  ------ Instantiation
% 11.73/2.06  
% 11.73/2.06  inst_num_of_clauses:                    3576
% 11.73/2.06  inst_num_in_passive:                    1590
% 11.73/2.06  inst_num_in_active:                     811
% 11.73/2.06  inst_num_in_unprocessed:                1174
% 11.73/2.06  inst_num_of_loops:                      1110
% 11.73/2.06  inst_num_of_learning_restarts:          0
% 11.73/2.06  inst_num_moves_active_passive:          293
% 11.73/2.06  inst_lit_activity:                      0
% 11.73/2.06  inst_lit_activity_moves:                1
% 11.73/2.06  inst_num_tautologies:                   0
% 11.73/2.06  inst_num_prop_implied:                  0
% 11.73/2.06  inst_num_existing_simplified:           0
% 11.73/2.06  inst_num_eq_res_simplified:             0
% 11.73/2.06  inst_num_child_elim:                    0
% 11.73/2.06  inst_num_of_dismatching_blockings:      972
% 11.73/2.06  inst_num_of_non_proper_insts:           3335
% 11.73/2.06  inst_num_of_duplicates:                 0
% 11.73/2.06  inst_inst_num_from_inst_to_res:         0
% 11.73/2.06  inst_dismatching_checking_time:         0.
% 11.73/2.06  
% 11.73/2.06  ------ Resolution
% 11.73/2.06  
% 11.73/2.06  res_num_of_clauses:                     0
% 11.73/2.06  res_num_in_passive:                     0
% 11.73/2.06  res_num_in_active:                      0
% 11.73/2.06  res_num_of_loops:                       60
% 11.73/2.06  res_forward_subset_subsumed:            1165
% 11.73/2.06  res_backward_subset_subsumed:           0
% 11.73/2.06  res_forward_subsumed:                   0
% 11.73/2.06  res_backward_subsumed:                  0
% 11.73/2.06  res_forward_subsumption_resolution:     0
% 11.73/2.06  res_backward_subsumption_resolution:    0
% 11.73/2.06  res_clause_to_clause_subsumption:       69631
% 11.73/2.06  res_orphan_elimination:                 0
% 11.73/2.06  res_tautology_del:                      323
% 11.73/2.06  res_num_eq_res_simplified:              0
% 11.73/2.06  res_num_sel_changes:                    0
% 11.73/2.06  res_moves_from_active_to_pass:          0
% 11.73/2.06  
% 11.73/2.06  ------ Superposition
% 11.73/2.06  
% 11.73/2.06  sup_time_total:                         0.
% 11.73/2.06  sup_time_generating:                    0.
% 11.73/2.06  sup_time_sim_full:                      0.
% 11.73/2.06  sup_time_sim_immed:                     0.
% 11.73/2.06  
% 11.73/2.06  sup_num_of_clauses:                     4023
% 11.73/2.06  sup_num_in_active:                      171
% 11.73/2.06  sup_num_in_passive:                     3852
% 11.73/2.06  sup_num_of_loops:                       220
% 11.73/2.06  sup_fw_superposition:                   9780
% 11.73/2.06  sup_bw_superposition:                   7520
% 11.73/2.06  sup_immediate_simplified:               10108
% 11.73/2.06  sup_given_eliminated:                   15
% 11.73/2.06  comparisons_done:                       0
% 11.73/2.06  comparisons_avoided:                    0
% 11.73/2.06  
% 11.73/2.06  ------ Simplifications
% 11.73/2.06  
% 11.73/2.06  
% 11.73/2.06  sim_fw_subset_subsumed:                 7
% 11.73/2.06  sim_bw_subset_subsumed:                 0
% 11.73/2.06  sim_fw_subsumed:                        1493
% 11.73/2.06  sim_bw_subsumed:                        202
% 11.73/2.06  sim_fw_subsumption_res:                 0
% 11.73/2.06  sim_bw_subsumption_res:                 0
% 11.73/2.06  sim_tautology_del:                      9
% 11.73/2.06  sim_eq_tautology_del:                   2971
% 11.73/2.06  sim_eq_res_simp:                        19
% 11.73/2.06  sim_fw_demodulated:                     6601
% 11.73/2.06  sim_bw_demodulated:                     161
% 11.73/2.06  sim_light_normalised:                   5946
% 11.73/2.06  sim_joinable_taut:                      214
% 11.73/2.06  sim_joinable_simp:                      0
% 11.73/2.06  sim_ac_normalised:                      0
% 11.73/2.06  sim_smt_subsumption:                    0
% 11.73/2.06  
%------------------------------------------------------------------------------
