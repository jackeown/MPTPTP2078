%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0092+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:28 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 (  80 expanded)
%              Number of equality atoms :   37 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_62,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_71,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_62])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_75,plain,
    ( k3_xboole_0(X0_36,X1_36) = k3_xboole_0(X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_73,plain,
    ( k4_xboole_0(k3_xboole_0(X0_36,X1_36),X0_37) = k3_xboole_0(X0_36,k4_xboole_0(X1_36,X0_37)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_96,plain,
    ( k4_xboole_0(k3_xboole_0(X0_36,X1_36),X0_37) = k3_xboole_0(X1_36,k4_xboole_0(X0_36,X0_37)) ),
    inference(superposition,[status(thm)],[c_75,c_73])).

cnf(c_106,plain,
    ( k3_xboole_0(X0_36,k4_xboole_0(X1_36,X0_37)) = k3_xboole_0(X1_36,k4_xboole_0(X0_36,X0_37)) ),
    inference(superposition,[status(thm)],[c_96,c_73])).

cnf(c_118,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(X0_36,sK1)) = k3_xboole_0(X0_36,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_71,c_106])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_74,plain,
    ( k3_xboole_0(X0_36,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_135,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(X0_36,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_118,c_74])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_55,plain,
    ( k4_xboole_0(sK2,sK1) != X0
    | k3_xboole_0(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_56,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_55])).

cnf(c_72,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_136,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_135,c_72])).

cnf(c_273,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_136])).


%------------------------------------------------------------------------------
