%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:54 EST 2020

% Result     : Theorem 27.42s
% Output     : CNFRefutation 27.42s
% Verified   : 
% Statistics : Number of formulae       :  167 (2630 expanded)
%              Number of clauses        :  129 (1028 expanded)
%              Number of leaves         :   13 ( 615 expanded)
%              Depth                    :   31
%              Number of atoms          :  197 (3873 expanded)
%              Number of equality atoms :  152 (2272 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f35,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f36,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f31,f31])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f37,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_326,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_330,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1777,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_326,c_330])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2004,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1777,c_8])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_785,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_1877,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_785])).

cnf(c_2977,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1877])).

cnf(c_36115,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2004,c_2977])).

cnf(c_337,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_2716,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1777,c_337])).

cnf(c_3207,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_337,c_2716])).

cnf(c_4619,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3,c_3207])).

cnf(c_4640,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4619,c_1777])).

cnf(c_4661,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_4640,c_8])).

cnf(c_2984,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1877,c_8])).

cnf(c_3014,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_2984,c_8])).

cnf(c_4685,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_4661,c_3014])).

cnf(c_36486,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_36115,c_1777,c_4685])).

cnf(c_36572,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X0,sK1))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_36486])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_110,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_109])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_103,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_104,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_331,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_104,c_6])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_744,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_331,c_7])).

cnf(c_1239,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_744])).

cnf(c_1241,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_744])).

cnf(c_1254,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1241,c_331])).

cnf(c_1346,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1239,c_1254])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_757,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_70979,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1346,c_757])).

cnf(c_746,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_1330,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_746,c_331])).

cnf(c_1328,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_746,c_1])).

cnf(c_55181,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1330,c_1328])).

cnf(c_55395,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_55181,c_6,c_331])).

cnf(c_55499,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_55395,c_6])).

cnf(c_71261,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_70979,c_7,c_55499])).

cnf(c_71543,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_110,c_71261])).

cnf(c_72014,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_71543,c_6])).

cnf(c_72126,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_72014,c_7])).

cnf(c_72541,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_36572,c_72126])).

cnf(c_72839,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_72541,c_72126])).

cnf(c_743,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_110,c_7])).

cnf(c_801,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_743])).

cnf(c_1246,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_744,c_801])).

cnf(c_803,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_3,c_743])).

cnf(c_806,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_803,c_110])).

cnf(c_1339,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1246,c_806])).

cnf(c_760,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_36647,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_36486,c_760])).

cnf(c_41205,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1339,c_36647])).

cnf(c_747,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_331])).

cnf(c_1360,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_747])).

cnf(c_338,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_3865,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1777,c_338])).

cnf(c_6887,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK0,X1),k4_xboole_0(k2_xboole_0(sK0,X1),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_3865,c_757])).

cnf(c_18328,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1360,c_6887])).

cnf(c_6876,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0))) = k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1777,c_757])).

cnf(c_7584,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0))),X1) = k4_xboole_0(k4_xboole_0(X0,sK0),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) ),
    inference(superposition,[status(thm)],[c_6876,c_7])).

cnf(c_15935,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0)),X0) = k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_331,c_7584])).

cnf(c_1257,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1254,c_744])).

cnf(c_8495,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_760])).

cnf(c_16232,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15935,c_6,c_7,c_1257,c_4685,c_8495])).

cnf(c_18559,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18328,c_6,c_7,c_331,c_746,c_4685,c_16232])).

cnf(c_18863,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18559,c_1])).

cnf(c_1363,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_331,c_747])).

cnf(c_18906,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_18863,c_6,c_1363])).

cnf(c_19008,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_18906,c_8])).

cnf(c_2185,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_2004])).

cnf(c_19576,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_19008,c_2185])).

cnf(c_19586,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19576,c_1777])).

cnf(c_804,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_743,c_7])).

cnf(c_805,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_804,c_7])).

cnf(c_1382,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_747,c_805])).

cnf(c_1332,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_746,c_805])).

cnf(c_1334,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1332,c_746])).

cnf(c_1335,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1334,c_743,c_1254])).

cnf(c_1385,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1382,c_1335])).

cnf(c_19663,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19586,c_1385])).

cnf(c_2978,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_785,c_1877])).

cnf(c_3019,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2978,c_3])).

cnf(c_5509,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3019])).

cnf(c_18345,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))),k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))),k4_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_5509,c_6887])).

cnf(c_18546,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(sK2,k2_xboole_0(sK1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_18345,c_2716,c_4685])).

cnf(c_23195,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_331,c_18546])).

cnf(c_23364,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_23195,c_7,c_19586])).

cnf(c_23536,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1777,c_23364])).

cnf(c_18332,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3,c_6887])).

cnf(c_2979,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_1777,c_1877])).

cnf(c_3018,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2979,c_3])).

cnf(c_6882,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_3018,c_757])).

cnf(c_761,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_762,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_761,c_7])).

cnf(c_10399,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_3018,c_762])).

cnf(c_10606,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10399,c_747])).

cnf(c_18553,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18332,c_1777,c_6882,c_10606])).

cnf(c_23666,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23536,c_18553])).

cnf(c_23850,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_23666,c_1])).

cnf(c_23914,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_23850,c_6,c_16232])).

cnf(c_1329,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_746,c_7])).

cnf(c_1336,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1329,c_7])).

cnf(c_27867,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1336,c_7])).

cnf(c_741,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_1218,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_741,c_7])).

cnf(c_1228,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1218,c_7])).

cnf(c_26666,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_338,c_1228])).

cnf(c_27893,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X3,X2)) ),
    inference(light_normalisation,[status(thm)],[c_27867,c_26666])).

cnf(c_41991,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_41205,c_6,c_1254,c_1777,c_19663,c_23914,c_27893])).

cnf(c_72840,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_72839,c_41991])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_329,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1150,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_329])).

cnf(c_72969,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_72840,c_1150])).

cnf(c_72990,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72969,c_6])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72990,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 27.42/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.42/4.00  
% 27.42/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.42/4.00  
% 27.42/4.00  ------  iProver source info
% 27.42/4.00  
% 27.42/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.42/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.42/4.00  git: non_committed_changes: false
% 27.42/4.00  git: last_make_outside_of_git: false
% 27.42/4.00  
% 27.42/4.00  ------ 
% 27.42/4.00  
% 27.42/4.00  ------ Input Options
% 27.42/4.00  
% 27.42/4.00  --out_options                           all
% 27.42/4.00  --tptp_safe_out                         true
% 27.42/4.00  --problem_path                          ""
% 27.42/4.00  --include_path                          ""
% 27.42/4.00  --clausifier                            res/vclausify_rel
% 27.42/4.00  --clausifier_options                    ""
% 27.42/4.00  --stdin                                 false
% 27.42/4.00  --stats_out                             all
% 27.42/4.00  
% 27.42/4.00  ------ General Options
% 27.42/4.00  
% 27.42/4.00  --fof                                   false
% 27.42/4.00  --time_out_real                         305.
% 27.42/4.00  --time_out_virtual                      -1.
% 27.42/4.00  --symbol_type_check                     false
% 27.42/4.00  --clausify_out                          false
% 27.42/4.00  --sig_cnt_out                           false
% 27.42/4.00  --trig_cnt_out                          false
% 27.42/4.00  --trig_cnt_out_tolerance                1.
% 27.42/4.00  --trig_cnt_out_sk_spl                   false
% 27.42/4.00  --abstr_cl_out                          false
% 27.42/4.00  
% 27.42/4.00  ------ Global Options
% 27.42/4.00  
% 27.42/4.00  --schedule                              default
% 27.42/4.00  --add_important_lit                     false
% 27.42/4.00  --prop_solver_per_cl                    1000
% 27.42/4.00  --min_unsat_core                        false
% 27.42/4.00  --soft_assumptions                      false
% 27.42/4.00  --soft_lemma_size                       3
% 27.42/4.00  --prop_impl_unit_size                   0
% 27.42/4.00  --prop_impl_unit                        []
% 27.42/4.00  --share_sel_clauses                     true
% 27.42/4.00  --reset_solvers                         false
% 27.42/4.00  --bc_imp_inh                            [conj_cone]
% 27.42/4.00  --conj_cone_tolerance                   3.
% 27.42/4.00  --extra_neg_conj                        none
% 27.42/4.00  --large_theory_mode                     true
% 27.42/4.00  --prolific_symb_bound                   200
% 27.42/4.00  --lt_threshold                          2000
% 27.42/4.00  --clause_weak_htbl                      true
% 27.42/4.00  --gc_record_bc_elim                     false
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing Options
% 27.42/4.00  
% 27.42/4.00  --preprocessing_flag                    true
% 27.42/4.00  --time_out_prep_mult                    0.1
% 27.42/4.00  --splitting_mode                        input
% 27.42/4.00  --splitting_grd                         true
% 27.42/4.00  --splitting_cvd                         false
% 27.42/4.00  --splitting_cvd_svl                     false
% 27.42/4.00  --splitting_nvd                         32
% 27.42/4.00  --sub_typing                            true
% 27.42/4.00  --prep_gs_sim                           true
% 27.42/4.00  --prep_unflatten                        true
% 27.42/4.00  --prep_res_sim                          true
% 27.42/4.00  --prep_upred                            true
% 27.42/4.00  --prep_sem_filter                       exhaustive
% 27.42/4.00  --prep_sem_filter_out                   false
% 27.42/4.00  --pred_elim                             true
% 27.42/4.00  --res_sim_input                         true
% 27.42/4.00  --eq_ax_congr_red                       true
% 27.42/4.00  --pure_diseq_elim                       true
% 27.42/4.00  --brand_transform                       false
% 27.42/4.00  --non_eq_to_eq                          false
% 27.42/4.00  --prep_def_merge                        true
% 27.42/4.00  --prep_def_merge_prop_impl              false
% 27.42/4.00  --prep_def_merge_mbd                    true
% 27.42/4.00  --prep_def_merge_tr_red                 false
% 27.42/4.00  --prep_def_merge_tr_cl                  false
% 27.42/4.00  --smt_preprocessing                     true
% 27.42/4.00  --smt_ac_axioms                         fast
% 27.42/4.00  --preprocessed_out                      false
% 27.42/4.00  --preprocessed_stats                    false
% 27.42/4.00  
% 27.42/4.00  ------ Abstraction refinement Options
% 27.42/4.00  
% 27.42/4.00  --abstr_ref                             []
% 27.42/4.00  --abstr_ref_prep                        false
% 27.42/4.00  --abstr_ref_until_sat                   false
% 27.42/4.00  --abstr_ref_sig_restrict                funpre
% 27.42/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.00  --abstr_ref_under                       []
% 27.42/4.00  
% 27.42/4.00  ------ SAT Options
% 27.42/4.00  
% 27.42/4.00  --sat_mode                              false
% 27.42/4.00  --sat_fm_restart_options                ""
% 27.42/4.00  --sat_gr_def                            false
% 27.42/4.00  --sat_epr_types                         true
% 27.42/4.00  --sat_non_cyclic_types                  false
% 27.42/4.00  --sat_finite_models                     false
% 27.42/4.00  --sat_fm_lemmas                         false
% 27.42/4.00  --sat_fm_prep                           false
% 27.42/4.00  --sat_fm_uc_incr                        true
% 27.42/4.00  --sat_out_model                         small
% 27.42/4.00  --sat_out_clauses                       false
% 27.42/4.00  
% 27.42/4.00  ------ QBF Options
% 27.42/4.00  
% 27.42/4.00  --qbf_mode                              false
% 27.42/4.00  --qbf_elim_univ                         false
% 27.42/4.00  --qbf_dom_inst                          none
% 27.42/4.00  --qbf_dom_pre_inst                      false
% 27.42/4.00  --qbf_sk_in                             false
% 27.42/4.00  --qbf_pred_elim                         true
% 27.42/4.00  --qbf_split                             512
% 27.42/4.00  
% 27.42/4.00  ------ BMC1 Options
% 27.42/4.00  
% 27.42/4.00  --bmc1_incremental                      false
% 27.42/4.00  --bmc1_axioms                           reachable_all
% 27.42/4.00  --bmc1_min_bound                        0
% 27.42/4.00  --bmc1_max_bound                        -1
% 27.42/4.00  --bmc1_max_bound_default                -1
% 27.42/4.00  --bmc1_symbol_reachability              true
% 27.42/4.00  --bmc1_property_lemmas                  false
% 27.42/4.00  --bmc1_k_induction                      false
% 27.42/4.00  --bmc1_non_equiv_states                 false
% 27.42/4.00  --bmc1_deadlock                         false
% 27.42/4.00  --bmc1_ucm                              false
% 27.42/4.00  --bmc1_add_unsat_core                   none
% 27.42/4.00  --bmc1_unsat_core_children              false
% 27.42/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.00  --bmc1_out_stat                         full
% 27.42/4.00  --bmc1_ground_init                      false
% 27.42/4.00  --bmc1_pre_inst_next_state              false
% 27.42/4.00  --bmc1_pre_inst_state                   false
% 27.42/4.00  --bmc1_pre_inst_reach_state             false
% 27.42/4.00  --bmc1_out_unsat_core                   false
% 27.42/4.00  --bmc1_aig_witness_out                  false
% 27.42/4.00  --bmc1_verbose                          false
% 27.42/4.00  --bmc1_dump_clauses_tptp                false
% 27.42/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.00  --bmc1_dump_file                        -
% 27.42/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.00  --bmc1_ucm_extend_mode                  1
% 27.42/4.00  --bmc1_ucm_init_mode                    2
% 27.42/4.00  --bmc1_ucm_cone_mode                    none
% 27.42/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.00  --bmc1_ucm_relax_model                  4
% 27.42/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.00  --bmc1_ucm_layered_model                none
% 27.42/4.00  --bmc1_ucm_max_lemma_size               10
% 27.42/4.00  
% 27.42/4.00  ------ AIG Options
% 27.42/4.00  
% 27.42/4.00  --aig_mode                              false
% 27.42/4.00  
% 27.42/4.00  ------ Instantiation Options
% 27.42/4.00  
% 27.42/4.00  --instantiation_flag                    true
% 27.42/4.00  --inst_sos_flag                         true
% 27.42/4.00  --inst_sos_phase                        true
% 27.42/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.00  --inst_lit_sel_side                     num_symb
% 27.42/4.00  --inst_solver_per_active                1400
% 27.42/4.00  --inst_solver_calls_frac                1.
% 27.42/4.00  --inst_passive_queue_type               priority_queues
% 27.42/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.00  --inst_passive_queues_freq              [25;2]
% 27.42/4.00  --inst_dismatching                      true
% 27.42/4.00  --inst_eager_unprocessed_to_passive     true
% 27.42/4.00  --inst_prop_sim_given                   true
% 27.42/4.00  --inst_prop_sim_new                     false
% 27.42/4.00  --inst_subs_new                         false
% 27.42/4.00  --inst_eq_res_simp                      false
% 27.42/4.00  --inst_subs_given                       false
% 27.42/4.00  --inst_orphan_elimination               true
% 27.42/4.00  --inst_learning_loop_flag               true
% 27.42/4.00  --inst_learning_start                   3000
% 27.42/4.00  --inst_learning_factor                  2
% 27.42/4.00  --inst_start_prop_sim_after_learn       3
% 27.42/4.00  --inst_sel_renew                        solver
% 27.42/4.00  --inst_lit_activity_flag                true
% 27.42/4.00  --inst_restr_to_given                   false
% 27.42/4.00  --inst_activity_threshold               500
% 27.42/4.00  --inst_out_proof                        true
% 27.42/4.00  
% 27.42/4.00  ------ Resolution Options
% 27.42/4.00  
% 27.42/4.00  --resolution_flag                       true
% 27.42/4.00  --res_lit_sel                           adaptive
% 27.42/4.00  --res_lit_sel_side                      none
% 27.42/4.00  --res_ordering                          kbo
% 27.42/4.00  --res_to_prop_solver                    active
% 27.42/4.00  --res_prop_simpl_new                    false
% 27.42/4.00  --res_prop_simpl_given                  true
% 27.42/4.00  --res_passive_queue_type                priority_queues
% 27.42/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.00  --res_passive_queues_freq               [15;5]
% 27.42/4.00  --res_forward_subs                      full
% 27.42/4.00  --res_backward_subs                     full
% 27.42/4.00  --res_forward_subs_resolution           true
% 27.42/4.00  --res_backward_subs_resolution          true
% 27.42/4.00  --res_orphan_elimination                true
% 27.42/4.00  --res_time_limit                        2.
% 27.42/4.00  --res_out_proof                         true
% 27.42/4.00  
% 27.42/4.00  ------ Superposition Options
% 27.42/4.00  
% 27.42/4.00  --superposition_flag                    true
% 27.42/4.00  --sup_passive_queue_type                priority_queues
% 27.42/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.00  --demod_completeness_check              fast
% 27.42/4.00  --demod_use_ground                      true
% 27.42/4.00  --sup_to_prop_solver                    passive
% 27.42/4.00  --sup_prop_simpl_new                    true
% 27.42/4.00  --sup_prop_simpl_given                  true
% 27.42/4.00  --sup_fun_splitting                     true
% 27.42/4.00  --sup_smt_interval                      50000
% 27.42/4.00  
% 27.42/4.00  ------ Superposition Simplification Setup
% 27.42/4.00  
% 27.42/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.42/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.42/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.42/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.42/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.42/4.00  --sup_immed_triv                        [TrivRules]
% 27.42/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_immed_bw_main                     []
% 27.42/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.42/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_input_bw                          []
% 27.42/4.00  
% 27.42/4.00  ------ Combination Options
% 27.42/4.00  
% 27.42/4.00  --comb_res_mult                         3
% 27.42/4.00  --comb_sup_mult                         2
% 27.42/4.00  --comb_inst_mult                        10
% 27.42/4.00  
% 27.42/4.00  ------ Debug Options
% 27.42/4.00  
% 27.42/4.00  --dbg_backtrace                         false
% 27.42/4.00  --dbg_dump_prop_clauses                 false
% 27.42/4.00  --dbg_dump_prop_clauses_file            -
% 27.42/4.00  --dbg_out_stat                          false
% 27.42/4.00  ------ Parsing...
% 27.42/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.42/4.00  ------ Proving...
% 27.42/4.00  ------ Problem Properties 
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  clauses                                 13
% 27.42/4.00  conjectures                             2
% 27.42/4.00  EPR                                     1
% 27.42/4.00  Horn                                    13
% 27.42/4.00  unary                                   12
% 27.42/4.00  binary                                  1
% 27.42/4.00  lits                                    14
% 27.42/4.00  lits eq                                 9
% 27.42/4.00  fd_pure                                 0
% 27.42/4.00  fd_pseudo                               0
% 27.42/4.00  fd_cond                                 0
% 27.42/4.00  fd_pseudo_cond                          0
% 27.42/4.00  AC symbols                              1
% 27.42/4.00  
% 27.42/4.00  ------ Schedule dynamic 5 is on 
% 27.42/4.00  
% 27.42/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  ------ 
% 27.42/4.00  Current options:
% 27.42/4.00  ------ 
% 27.42/4.00  
% 27.42/4.00  ------ Input Options
% 27.42/4.00  
% 27.42/4.00  --out_options                           all
% 27.42/4.00  --tptp_safe_out                         true
% 27.42/4.00  --problem_path                          ""
% 27.42/4.00  --include_path                          ""
% 27.42/4.00  --clausifier                            res/vclausify_rel
% 27.42/4.00  --clausifier_options                    ""
% 27.42/4.00  --stdin                                 false
% 27.42/4.00  --stats_out                             all
% 27.42/4.00  
% 27.42/4.00  ------ General Options
% 27.42/4.00  
% 27.42/4.00  --fof                                   false
% 27.42/4.00  --time_out_real                         305.
% 27.42/4.00  --time_out_virtual                      -1.
% 27.42/4.00  --symbol_type_check                     false
% 27.42/4.00  --clausify_out                          false
% 27.42/4.00  --sig_cnt_out                           false
% 27.42/4.00  --trig_cnt_out                          false
% 27.42/4.00  --trig_cnt_out_tolerance                1.
% 27.42/4.00  --trig_cnt_out_sk_spl                   false
% 27.42/4.00  --abstr_cl_out                          false
% 27.42/4.00  
% 27.42/4.00  ------ Global Options
% 27.42/4.00  
% 27.42/4.00  --schedule                              default
% 27.42/4.00  --add_important_lit                     false
% 27.42/4.00  --prop_solver_per_cl                    1000
% 27.42/4.00  --min_unsat_core                        false
% 27.42/4.00  --soft_assumptions                      false
% 27.42/4.00  --soft_lemma_size                       3
% 27.42/4.00  --prop_impl_unit_size                   0
% 27.42/4.00  --prop_impl_unit                        []
% 27.42/4.00  --share_sel_clauses                     true
% 27.42/4.00  --reset_solvers                         false
% 27.42/4.00  --bc_imp_inh                            [conj_cone]
% 27.42/4.00  --conj_cone_tolerance                   3.
% 27.42/4.00  --extra_neg_conj                        none
% 27.42/4.00  --large_theory_mode                     true
% 27.42/4.00  --prolific_symb_bound                   200
% 27.42/4.00  --lt_threshold                          2000
% 27.42/4.00  --clause_weak_htbl                      true
% 27.42/4.00  --gc_record_bc_elim                     false
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing Options
% 27.42/4.00  
% 27.42/4.00  --preprocessing_flag                    true
% 27.42/4.00  --time_out_prep_mult                    0.1
% 27.42/4.00  --splitting_mode                        input
% 27.42/4.00  --splitting_grd                         true
% 27.42/4.00  --splitting_cvd                         false
% 27.42/4.00  --splitting_cvd_svl                     false
% 27.42/4.00  --splitting_nvd                         32
% 27.42/4.00  --sub_typing                            true
% 27.42/4.00  --prep_gs_sim                           true
% 27.42/4.00  --prep_unflatten                        true
% 27.42/4.00  --prep_res_sim                          true
% 27.42/4.00  --prep_upred                            true
% 27.42/4.00  --prep_sem_filter                       exhaustive
% 27.42/4.00  --prep_sem_filter_out                   false
% 27.42/4.00  --pred_elim                             true
% 27.42/4.00  --res_sim_input                         true
% 27.42/4.00  --eq_ax_congr_red                       true
% 27.42/4.00  --pure_diseq_elim                       true
% 27.42/4.00  --brand_transform                       false
% 27.42/4.00  --non_eq_to_eq                          false
% 27.42/4.00  --prep_def_merge                        true
% 27.42/4.00  --prep_def_merge_prop_impl              false
% 27.42/4.00  --prep_def_merge_mbd                    true
% 27.42/4.00  --prep_def_merge_tr_red                 false
% 27.42/4.00  --prep_def_merge_tr_cl                  false
% 27.42/4.00  --smt_preprocessing                     true
% 27.42/4.00  --smt_ac_axioms                         fast
% 27.42/4.00  --preprocessed_out                      false
% 27.42/4.00  --preprocessed_stats                    false
% 27.42/4.00  
% 27.42/4.00  ------ Abstraction refinement Options
% 27.42/4.00  
% 27.42/4.00  --abstr_ref                             []
% 27.42/4.00  --abstr_ref_prep                        false
% 27.42/4.00  --abstr_ref_until_sat                   false
% 27.42/4.00  --abstr_ref_sig_restrict                funpre
% 27.42/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.00  --abstr_ref_under                       []
% 27.42/4.00  
% 27.42/4.00  ------ SAT Options
% 27.42/4.00  
% 27.42/4.00  --sat_mode                              false
% 27.42/4.00  --sat_fm_restart_options                ""
% 27.42/4.00  --sat_gr_def                            false
% 27.42/4.00  --sat_epr_types                         true
% 27.42/4.00  --sat_non_cyclic_types                  false
% 27.42/4.00  --sat_finite_models                     false
% 27.42/4.00  --sat_fm_lemmas                         false
% 27.42/4.00  --sat_fm_prep                           false
% 27.42/4.00  --sat_fm_uc_incr                        true
% 27.42/4.00  --sat_out_model                         small
% 27.42/4.00  --sat_out_clauses                       false
% 27.42/4.00  
% 27.42/4.00  ------ QBF Options
% 27.42/4.00  
% 27.42/4.00  --qbf_mode                              false
% 27.42/4.00  --qbf_elim_univ                         false
% 27.42/4.00  --qbf_dom_inst                          none
% 27.42/4.00  --qbf_dom_pre_inst                      false
% 27.42/4.00  --qbf_sk_in                             false
% 27.42/4.00  --qbf_pred_elim                         true
% 27.42/4.00  --qbf_split                             512
% 27.42/4.00  
% 27.42/4.00  ------ BMC1 Options
% 27.42/4.00  
% 27.42/4.00  --bmc1_incremental                      false
% 27.42/4.00  --bmc1_axioms                           reachable_all
% 27.42/4.00  --bmc1_min_bound                        0
% 27.42/4.00  --bmc1_max_bound                        -1
% 27.42/4.00  --bmc1_max_bound_default                -1
% 27.42/4.00  --bmc1_symbol_reachability              true
% 27.42/4.00  --bmc1_property_lemmas                  false
% 27.42/4.00  --bmc1_k_induction                      false
% 27.42/4.00  --bmc1_non_equiv_states                 false
% 27.42/4.00  --bmc1_deadlock                         false
% 27.42/4.00  --bmc1_ucm                              false
% 27.42/4.00  --bmc1_add_unsat_core                   none
% 27.42/4.00  --bmc1_unsat_core_children              false
% 27.42/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.00  --bmc1_out_stat                         full
% 27.42/4.00  --bmc1_ground_init                      false
% 27.42/4.00  --bmc1_pre_inst_next_state              false
% 27.42/4.00  --bmc1_pre_inst_state                   false
% 27.42/4.00  --bmc1_pre_inst_reach_state             false
% 27.42/4.00  --bmc1_out_unsat_core                   false
% 27.42/4.00  --bmc1_aig_witness_out                  false
% 27.42/4.00  --bmc1_verbose                          false
% 27.42/4.00  --bmc1_dump_clauses_tptp                false
% 27.42/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.00  --bmc1_dump_file                        -
% 27.42/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.00  --bmc1_ucm_extend_mode                  1
% 27.42/4.00  --bmc1_ucm_init_mode                    2
% 27.42/4.00  --bmc1_ucm_cone_mode                    none
% 27.42/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.00  --bmc1_ucm_relax_model                  4
% 27.42/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.00  --bmc1_ucm_layered_model                none
% 27.42/4.00  --bmc1_ucm_max_lemma_size               10
% 27.42/4.00  
% 27.42/4.00  ------ AIG Options
% 27.42/4.00  
% 27.42/4.00  --aig_mode                              false
% 27.42/4.00  
% 27.42/4.00  ------ Instantiation Options
% 27.42/4.00  
% 27.42/4.00  --instantiation_flag                    true
% 27.42/4.00  --inst_sos_flag                         true
% 27.42/4.00  --inst_sos_phase                        true
% 27.42/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.00  --inst_lit_sel_side                     none
% 27.42/4.00  --inst_solver_per_active                1400
% 27.42/4.00  --inst_solver_calls_frac                1.
% 27.42/4.00  --inst_passive_queue_type               priority_queues
% 27.42/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.00  --inst_passive_queues_freq              [25;2]
% 27.42/4.00  --inst_dismatching                      true
% 27.42/4.00  --inst_eager_unprocessed_to_passive     true
% 27.42/4.00  --inst_prop_sim_given                   true
% 27.42/4.00  --inst_prop_sim_new                     false
% 27.42/4.00  --inst_subs_new                         false
% 27.42/4.00  --inst_eq_res_simp                      false
% 27.42/4.00  --inst_subs_given                       false
% 27.42/4.00  --inst_orphan_elimination               true
% 27.42/4.00  --inst_learning_loop_flag               true
% 27.42/4.00  --inst_learning_start                   3000
% 27.42/4.00  --inst_learning_factor                  2
% 27.42/4.00  --inst_start_prop_sim_after_learn       3
% 27.42/4.00  --inst_sel_renew                        solver
% 27.42/4.00  --inst_lit_activity_flag                true
% 27.42/4.00  --inst_restr_to_given                   false
% 27.42/4.00  --inst_activity_threshold               500
% 27.42/4.00  --inst_out_proof                        true
% 27.42/4.00  
% 27.42/4.00  ------ Resolution Options
% 27.42/4.00  
% 27.42/4.00  --resolution_flag                       false
% 27.42/4.00  --res_lit_sel                           adaptive
% 27.42/4.00  --res_lit_sel_side                      none
% 27.42/4.00  --res_ordering                          kbo
% 27.42/4.00  --res_to_prop_solver                    active
% 27.42/4.00  --res_prop_simpl_new                    false
% 27.42/4.00  --res_prop_simpl_given                  true
% 27.42/4.00  --res_passive_queue_type                priority_queues
% 27.42/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.00  --res_passive_queues_freq               [15;5]
% 27.42/4.00  --res_forward_subs                      full
% 27.42/4.00  --res_backward_subs                     full
% 27.42/4.00  --res_forward_subs_resolution           true
% 27.42/4.00  --res_backward_subs_resolution          true
% 27.42/4.00  --res_orphan_elimination                true
% 27.42/4.00  --res_time_limit                        2.
% 27.42/4.00  --res_out_proof                         true
% 27.42/4.00  
% 27.42/4.00  ------ Superposition Options
% 27.42/4.00  
% 27.42/4.00  --superposition_flag                    true
% 27.42/4.00  --sup_passive_queue_type                priority_queues
% 27.42/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.00  --demod_completeness_check              fast
% 27.42/4.00  --demod_use_ground                      true
% 27.42/4.00  --sup_to_prop_solver                    passive
% 27.42/4.00  --sup_prop_simpl_new                    true
% 27.42/4.00  --sup_prop_simpl_given                  true
% 27.42/4.00  --sup_fun_splitting                     true
% 27.42/4.00  --sup_smt_interval                      50000
% 27.42/4.00  
% 27.42/4.00  ------ Superposition Simplification Setup
% 27.42/4.00  
% 27.42/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.42/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.42/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.42/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.42/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.42/4.00  --sup_immed_triv                        [TrivRules]
% 27.42/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_immed_bw_main                     []
% 27.42/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.42/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.00  --sup_input_bw                          []
% 27.42/4.00  
% 27.42/4.00  ------ Combination Options
% 27.42/4.00  
% 27.42/4.00  --comb_res_mult                         3
% 27.42/4.00  --comb_sup_mult                         2
% 27.42/4.00  --comb_inst_mult                        10
% 27.42/4.00  
% 27.42/4.00  ------ Debug Options
% 27.42/4.00  
% 27.42/4.00  --dbg_backtrace                         false
% 27.42/4.00  --dbg_dump_prop_clauses                 false
% 27.42/4.00  --dbg_dump_prop_clauses_file            -
% 27.42/4.00  --dbg_out_stat                          false
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  ------ Proving...
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  % SZS status Theorem for theBenchmark.p
% 27.42/4.00  
% 27.42/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.42/4.00  
% 27.42/4.00  fof(f1,axiom,(
% 27.42/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f23,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f1])).
% 27.42/4.00  
% 27.42/4.00  fof(f13,conjecture,(
% 27.42/4.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f14,negated_conjecture,(
% 27.42/4.00    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 27.42/4.00    inference(negated_conjecture,[],[f13])).
% 27.42/4.00  
% 27.42/4.00  fof(f19,plain,(
% 27.42/4.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 27.42/4.00    inference(ennf_transformation,[],[f14])).
% 27.42/4.00  
% 27.42/4.00  fof(f20,plain,(
% 27.42/4.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.42/4.00    inference(flattening,[],[f19])).
% 27.42/4.00  
% 27.42/4.00  fof(f21,plain,(
% 27.42/4.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 27.42/4.00    introduced(choice_axiom,[])).
% 27.42/4.00  
% 27.42/4.00  fof(f22,plain,(
% 27.42/4.00    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 27.42/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 27.42/4.00  
% 27.42/4.00  fof(f35,plain,(
% 27.42/4.00    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 27.42/4.00    inference(cnf_transformation,[],[f22])).
% 27.42/4.00  
% 27.42/4.00  fof(f5,axiom,(
% 27.42/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f18,plain,(
% 27.42/4.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.42/4.00    inference(ennf_transformation,[],[f5])).
% 27.42/4.00  
% 27.42/4.00  fof(f27,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f18])).
% 27.42/4.00  
% 27.42/4.00  fof(f10,axiom,(
% 27.42/4.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f32,plain,(
% 27.42/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f10])).
% 27.42/4.00  
% 27.42/4.00  fof(f4,axiom,(
% 27.42/4.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f15,plain,(
% 27.42/4.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 27.42/4.00    inference(rectify,[],[f4])).
% 27.42/4.00  
% 27.42/4.00  fof(f26,plain,(
% 27.42/4.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 27.42/4.00    inference(cnf_transformation,[],[f15])).
% 27.42/4.00  
% 27.42/4.00  fof(f3,axiom,(
% 27.42/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f16,plain,(
% 27.42/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.42/4.00    inference(unused_predicate_definition_removal,[],[f3])).
% 27.42/4.00  
% 27.42/4.00  fof(f17,plain,(
% 27.42/4.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 27.42/4.00    inference(ennf_transformation,[],[f16])).
% 27.42/4.00  
% 27.42/4.00  fof(f25,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f17])).
% 27.42/4.00  
% 27.42/4.00  fof(f9,axiom,(
% 27.42/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f31,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.42/4.00    inference(cnf_transformation,[],[f9])).
% 27.42/4.00  
% 27.42/4.00  fof(f39,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 27.42/4.00    inference(definition_unfolding,[],[f25,f31])).
% 27.42/4.00  
% 27.42/4.00  fof(f36,plain,(
% 27.42/4.00    r1_xboole_0(sK0,sK2)),
% 27.42/4.00    inference(cnf_transformation,[],[f22])).
% 27.42/4.00  
% 27.42/4.00  fof(f11,axiom,(
% 27.42/4.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f33,plain,(
% 27.42/4.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f11])).
% 27.42/4.00  
% 27.42/4.00  fof(f7,axiom,(
% 27.42/4.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f29,plain,(
% 27.42/4.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.42/4.00    inference(cnf_transformation,[],[f7])).
% 27.42/4.00  
% 27.42/4.00  fof(f8,axiom,(
% 27.42/4.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f30,plain,(
% 27.42/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f8])).
% 27.42/4.00  
% 27.42/4.00  fof(f2,axiom,(
% 27.42/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f24,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f2])).
% 27.42/4.00  
% 27.42/4.00  fof(f38,plain,(
% 27.42/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.42/4.00    inference(definition_unfolding,[],[f24,f31,f31])).
% 27.42/4.00  
% 27.42/4.00  fof(f6,axiom,(
% 27.42/4.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 27.42/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.42/4.00  
% 27.42/4.00  fof(f28,plain,(
% 27.42/4.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 27.42/4.00    inference(cnf_transformation,[],[f6])).
% 27.42/4.00  
% 27.42/4.00  fof(f40,plain,(
% 27.42/4.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 27.42/4.00    inference(definition_unfolding,[],[f28,f31])).
% 27.42/4.00  
% 27.42/4.00  fof(f37,plain,(
% 27.42/4.00    ~r1_tarski(sK0,sK1)),
% 27.42/4.00    inference(cnf_transformation,[],[f22])).
% 27.42/4.00  
% 27.42/4.00  cnf(c_0,plain,
% 27.42/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.42/4.00      inference(cnf_transformation,[],[f23]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_13,negated_conjecture,
% 27.42/4.00      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(cnf_transformation,[],[f35]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_326,plain,
% 27.42/4.00      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 27.42/4.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_4,plain,
% 27.42/4.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.42/4.00      inference(cnf_transformation,[],[f27]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_330,plain,
% 27.42/4.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 27.42/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1777,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_326,c_330]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_8,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(cnf_transformation,[],[f32]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2004,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3,plain,
% 27.42/4.00      ( k2_xboole_0(X0,X0) = X0 ),
% 27.42/4.00      inference(cnf_transformation,[],[f26]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_785,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1877,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_785]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2977,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_8,c_1877]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_36115,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_2004,c_2977]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_337,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2716,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_337]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3207,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_337,c_2716]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_4619,plain,
% 27.42/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3,c_3207]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_4640,plain,
% 27.42/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_4619,c_1777]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_4661,plain,
% 27.42/4.00      ( k2_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_4640,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2984,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1877,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3014,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_2984,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_4685,plain,
% 27.42/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_4661,c_3014]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_36486,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(light_normalisation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_36115,c_1777,c_4685]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_36572,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X0,sK1))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_36486]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2,plain,
% 27.42/4.00      ( ~ r1_xboole_0(X0,X1)
% 27.42/4.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.42/4.00      inference(cnf_transformation,[],[f39]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_12,negated_conjecture,
% 27.42/4.00      ( r1_xboole_0(sK0,sK2) ),
% 27.42/4.00      inference(cnf_transformation,[],[f36]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_109,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 27.42/4.00      | sK2 != X1
% 27.42/4.00      | sK0 != X0 ),
% 27.42/4.00      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_110,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 27.42/4.00      inference(unflattening,[status(thm)],[c_109]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_9,plain,
% 27.42/4.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 27.42/4.00      inference(cnf_transformation,[],[f33]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_103,plain,
% 27.42/4.00      ( X0 != X1
% 27.42/4.00      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
% 27.42/4.00      | k1_xboole_0 != X2 ),
% 27.42/4.00      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_104,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.42/4.00      inference(unflattening,[status(thm)],[c_103]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_6,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.42/4.00      inference(cnf_transformation,[],[f29]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_331,plain,
% 27.42/4.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_104,c_6]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_7,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(cnf_transformation,[],[f30]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_744,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_331,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1239,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k1_xboole_0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_744]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1241,plain,
% 27.42/4.00      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3,c_744]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1254,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1241,c_331]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1346,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_1239,c_1254]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.42/4.00      inference(cnf_transformation,[],[f38]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_757,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_70979,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1346,c_757]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_746,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1330,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_746,c_331]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1328,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_746,c_1]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_55181,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1330,c_1328]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_55395,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_55181,c_6,c_331]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_55499,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_55395,c_6]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_71261,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_70979,c_7,c_55499]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_71543,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_110,c_71261]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72014,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_71543,c_6]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72126,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_72014,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72541,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK2,sK1))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_36572,c_72126]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72839,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_72541,c_72126]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_743,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_110,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_801,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_743]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1246,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k1_xboole_0,sK0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_744,c_801]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_803,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3,c_743]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_806,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_803,c_110]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1339,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1246,c_806]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_760,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_36647,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(sK1,sK2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_36486,c_760]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_41205,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k2_xboole_0(sK1,sK2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1339,c_36647]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_747,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_7,c_331]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1360,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_6,c_747]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_338,plain,
% 27.42/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3865,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_338]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_6887,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK0,X1),k4_xboole_0(k2_xboole_0(sK0,X1),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3865,c_757]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18328,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1360,c_6887]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_6876,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0))) = k4_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_757]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_7584,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0))),X1) = k4_xboole_0(k4_xboole_0(X0,sK0),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),X1)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_6876,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_15935,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0)),X0) = k4_xboole_0(k4_xboole_0(sK0,sK0),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),X0)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_331,c_7584]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1257,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_1254,c_744]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_8495,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1,c_760]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_16232,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_15935,c_6,c_7,c_1257,c_4685,c_8495]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18559,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),sK0) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_18328,c_6,c_7,c_331,c_746,c_4685,c_16232]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18863,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_18559,c_1]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1363,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_331,c_747]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18906,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_18863,c_6,c_1363]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_19008,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(sK0,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_18906,c_8]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2185,plain,
% 27.42/4.00      ( k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_2004]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_19576,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_19008,c_2185]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_19586,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_19576,c_1777]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_804,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_743,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_805,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),X0),X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_804,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1382,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)))) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_747,c_805]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1332,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_746,c_805]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1334,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_1332,c_746]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1335,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1334,c_743,c_1254]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1385,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1382,c_1335]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_19663,plain,
% 27.42/4.00      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_19586,c_1385]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2978,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_785,c_1877]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3019,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_2978,c_3]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_5509,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_0,c_3019]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18345,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))),k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2))),k4_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_5509,c_6887]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18546,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK1,sK2)),k4_xboole_0(X1,k2_xboole_0(sK2,k2_xboole_0(sK1,X0)))) ),
% 27.42/4.00      inference(light_normalisation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_18345,c_2716,c_4685]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23195,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_331,c_18546]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23364,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,X0)),k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_23195,c_7,c_19586]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23536,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_23364]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18332,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3,c_6887]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_2979,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1777,c_1877]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_3018,plain,
% 27.42/4.00      ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_2979,c_3]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_6882,plain,
% 27.42/4.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3018,c_757]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_761,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_762,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_761,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_10399,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_3018,c_762]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_10606,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_10399,c_747]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_18553,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_18332,c_1777,c_6882,c_10606]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23666,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_23536,c_18553]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23850,plain,
% 27.42/4.00      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)),k1_xboole_0) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_23666,c_1]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_23914,plain,
% 27.42/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_23850,c_6,c_16232]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1329,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_746,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1336,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1329,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_27867,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1336,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_741,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1218,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_741,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1228,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_1218,c_7]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_26666,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X3,X2))) ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_338,c_1228]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_27893,plain,
% 27.42/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X3,X2)) ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_27867,c_26666]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_41991,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 27.42/4.00      inference(demodulation,
% 27.42/4.00                [status(thm)],
% 27.42/4.00                [c_41205,c_6,c_1254,c_1777,c_19663,c_23914,c_27893]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72840,plain,
% 27.42/4.00      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 27.42/4.00      inference(light_normalisation,[status(thm)],[c_72839,c_41991]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_5,plain,
% 27.42/4.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 27.42/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_329,plain,
% 27.42/4.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 27.42/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_1150,plain,
% 27.42/4.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_1,c_329]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72969,plain,
% 27.42/4.00      ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),sK1) = iProver_top ),
% 27.42/4.00      inference(superposition,[status(thm)],[c_72840,c_1150]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_72990,plain,
% 27.42/4.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 27.42/4.00      inference(demodulation,[status(thm)],[c_72969,c_6]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_11,negated_conjecture,
% 27.42/4.00      ( ~ r1_tarski(sK0,sK1) ),
% 27.42/4.00      inference(cnf_transformation,[],[f37]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(c_16,plain,
% 27.42/4.00      ( r1_tarski(sK0,sK1) != iProver_top ),
% 27.42/4.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.42/4.00  
% 27.42/4.00  cnf(contradiction,plain,
% 27.42/4.00      ( $false ),
% 27.42/4.00      inference(minisat,[status(thm)],[c_72990,c_16]) ).
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.42/4.00  
% 27.42/4.00  ------                               Statistics
% 27.42/4.00  
% 27.42/4.00  ------ General
% 27.42/4.00  
% 27.42/4.00  abstr_ref_over_cycles:                  0
% 27.42/4.00  abstr_ref_under_cycles:                 0
% 27.42/4.00  gc_basic_clause_elim:                   0
% 27.42/4.00  forced_gc_time:                         0
% 27.42/4.00  parsing_time:                           0.01
% 27.42/4.00  unif_index_cands_time:                  0.
% 27.42/4.00  unif_index_add_time:                    0.
% 27.42/4.00  orderings_time:                         0.
% 27.42/4.00  out_proof_time:                         0.013
% 27.42/4.00  total_time:                             3.134
% 27.42/4.00  num_of_symbols:                         39
% 27.42/4.00  num_of_terms:                           135915
% 27.42/4.00  
% 27.42/4.00  ------ Preprocessing
% 27.42/4.00  
% 27.42/4.00  num_of_splits:                          0
% 27.42/4.00  num_of_split_atoms:                     0
% 27.42/4.00  num_of_reused_defs:                     0
% 27.42/4.00  num_eq_ax_congr_red:                    0
% 27.42/4.00  num_of_sem_filtered_clauses:            1
% 27.42/4.00  num_of_subtypes:                        0
% 27.42/4.00  monotx_restored_types:                  0
% 27.42/4.00  sat_num_of_epr_types:                   0
% 27.42/4.00  sat_num_of_non_cyclic_types:            0
% 27.42/4.00  sat_guarded_non_collapsed_types:        0
% 27.42/4.00  num_pure_diseq_elim:                    0
% 27.42/4.00  simp_replaced_by:                       0
% 27.42/4.00  res_preprocessed:                       64
% 27.42/4.00  prep_upred:                             0
% 27.42/4.00  prep_unflattend:                        20
% 27.42/4.00  smt_new_axioms:                         0
% 27.42/4.00  pred_elim_cands:                        1
% 27.42/4.00  pred_elim:                              1
% 27.42/4.00  pred_elim_cl:                           1
% 27.42/4.00  pred_elim_cycles:                       3
% 27.42/4.00  merged_defs:                            0
% 27.42/4.00  merged_defs_ncl:                        0
% 27.42/4.00  bin_hyper_res:                          0
% 27.42/4.00  prep_cycles:                            4
% 27.42/4.00  pred_elim_time:                         0.002
% 27.42/4.00  splitting_time:                         0.
% 27.42/4.00  sem_filter_time:                        0.
% 27.42/4.00  monotx_time:                            0.
% 27.42/4.00  subtype_inf_time:                       0.
% 27.42/4.00  
% 27.42/4.00  ------ Problem properties
% 27.42/4.00  
% 27.42/4.00  clauses:                                13
% 27.42/4.00  conjectures:                            2
% 27.42/4.00  epr:                                    1
% 27.42/4.00  horn:                                   13
% 27.42/4.00  ground:                                 3
% 27.42/4.00  unary:                                  12
% 27.42/4.00  binary:                                 1
% 27.42/4.00  lits:                                   14
% 27.42/4.00  lits_eq:                                9
% 27.42/4.00  fd_pure:                                0
% 27.42/4.00  fd_pseudo:                              0
% 27.42/4.00  fd_cond:                                0
% 27.42/4.00  fd_pseudo_cond:                         0
% 27.42/4.00  ac_symbols:                             1
% 27.42/4.00  
% 27.42/4.00  ------ Propositional Solver
% 27.42/4.00  
% 27.42/4.00  prop_solver_calls:                      35
% 27.42/4.00  prop_fast_solver_calls:                 597
% 27.42/4.00  smt_solver_calls:                       0
% 27.42/4.00  smt_fast_solver_calls:                  0
% 27.42/4.00  prop_num_of_clauses:                    24701
% 27.42/4.00  prop_preprocess_simplified:             21833
% 27.42/4.00  prop_fo_subsumed:                       0
% 27.42/4.00  prop_solver_time:                       0.
% 27.42/4.00  smt_solver_time:                        0.
% 27.42/4.00  smt_fast_solver_time:                   0.
% 27.42/4.00  prop_fast_solver_time:                  0.
% 27.42/4.00  prop_unsat_core_time:                   0.003
% 27.42/4.00  
% 27.42/4.00  ------ QBF
% 27.42/4.00  
% 27.42/4.00  qbf_q_res:                              0
% 27.42/4.00  qbf_num_tautologies:                    0
% 27.42/4.00  qbf_prep_cycles:                        0
% 27.42/4.00  
% 27.42/4.00  ------ BMC1
% 27.42/4.00  
% 27.42/4.00  bmc1_current_bound:                     -1
% 27.42/4.00  bmc1_last_solved_bound:                 -1
% 27.42/4.00  bmc1_unsat_core_size:                   -1
% 27.42/4.00  bmc1_unsat_core_parents_size:           -1
% 27.42/4.00  bmc1_merge_next_fun:                    0
% 27.42/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.42/4.00  
% 27.42/4.00  ------ Instantiation
% 27.42/4.00  
% 27.42/4.00  inst_num_of_clauses:                    4657
% 27.42/4.00  inst_num_in_passive:                    1685
% 27.42/4.00  inst_num_in_active:                     1519
% 27.42/4.00  inst_num_in_unprocessed:                1456
% 27.42/4.00  inst_num_of_loops:                      1680
% 27.42/4.00  inst_num_of_learning_restarts:          0
% 27.42/4.00  inst_num_moves_active_passive:          156
% 27.42/4.00  inst_lit_activity:                      0
% 27.42/4.00  inst_lit_activity_moves:                1
% 27.42/4.00  inst_num_tautologies:                   0
% 27.42/4.00  inst_num_prop_implied:                  0
% 27.42/4.00  inst_num_existing_simplified:           0
% 27.42/4.00  inst_num_eq_res_simplified:             0
% 27.42/4.00  inst_num_child_elim:                    0
% 27.42/4.00  inst_num_of_dismatching_blockings:      2430
% 27.42/4.00  inst_num_of_non_proper_insts:           4397
% 27.42/4.00  inst_num_of_duplicates:                 0
% 27.42/4.00  inst_inst_num_from_inst_to_res:         0
% 27.42/4.00  inst_dismatching_checking_time:         0.
% 27.42/4.00  
% 27.42/4.00  ------ Resolution
% 27.42/4.00  
% 27.42/4.00  res_num_of_clauses:                     0
% 27.42/4.00  res_num_in_passive:                     0
% 27.42/4.00  res_num_in_active:                      0
% 27.42/4.00  res_num_of_loops:                       68
% 27.42/4.00  res_forward_subset_subsumed:            499
% 27.42/4.00  res_backward_subset_subsumed:           14
% 27.42/4.00  res_forward_subsumed:                   0
% 27.42/4.00  res_backward_subsumed:                  0
% 27.42/4.00  res_forward_subsumption_resolution:     0
% 27.42/4.00  res_backward_subsumption_resolution:    0
% 27.42/4.00  res_clause_to_clause_subsumption:       63598
% 27.42/4.00  res_orphan_elimination:                 0
% 27.42/4.00  res_tautology_del:                      130
% 27.42/4.00  res_num_eq_res_simplified:              0
% 27.42/4.00  res_num_sel_changes:                    0
% 27.42/4.00  res_moves_from_active_to_pass:          0
% 27.42/4.00  
% 27.42/4.00  ------ Superposition
% 27.42/4.00  
% 27.42/4.00  sup_time_total:                         0.
% 27.42/4.00  sup_time_generating:                    0.
% 27.42/4.00  sup_time_sim_full:                      0.
% 27.42/4.00  sup_time_sim_immed:                     0.
% 27.42/4.00  
% 27.42/4.00  sup_num_of_clauses:                     5432
% 27.42/4.00  sup_num_in_active:                      245
% 27.42/4.00  sup_num_in_passive:                     5187
% 27.42/4.00  sup_num_of_loops:                       334
% 27.42/4.00  sup_fw_superposition:                   14581
% 27.42/4.00  sup_bw_superposition:                   8486
% 27.42/4.00  sup_immediate_simplified:               12181
% 27.42/4.00  sup_given_eliminated:                   9
% 27.42/4.00  comparisons_done:                       0
% 27.42/4.00  comparisons_avoided:                    0
% 27.42/4.00  
% 27.42/4.00  ------ Simplifications
% 27.42/4.00  
% 27.42/4.00  
% 27.42/4.00  sim_fw_subset_subsumed:                 0
% 27.42/4.00  sim_bw_subset_subsumed:                 0
% 27.42/4.00  sim_fw_subsumed:                        1297
% 27.42/4.00  sim_bw_subsumed:                        171
% 27.42/4.00  sim_fw_subsumption_res:                 0
% 27.42/4.00  sim_bw_subsumption_res:                 0
% 27.42/4.00  sim_tautology_del:                      0
% 27.42/4.00  sim_eq_tautology_del:                   2742
% 27.42/4.00  sim_eq_res_simp:                        0
% 27.42/4.00  sim_fw_demodulated:                     13852
% 27.42/4.00  sim_bw_demodulated:                     198
% 27.42/4.00  sim_light_normalised:                   4659
% 27.42/4.00  sim_joinable_taut:                      416
% 27.42/4.00  sim_joinable_simp:                      0
% 27.42/4.00  sim_ac_normalised:                      0
% 27.42/4.00  sim_smt_subsumption:                    0
% 27.42/4.00  
%------------------------------------------------------------------------------
