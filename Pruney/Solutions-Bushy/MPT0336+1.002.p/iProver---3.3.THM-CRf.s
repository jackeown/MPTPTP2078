%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0336+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:02 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 246 expanded)
%              Number of clauses        :   59 ( 108 expanded)
%              Number of leaves         :   14 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  173 ( 574 expanded)
%              Number of equality atoms :  101 ( 193 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f21,plain,
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

fof(f22,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).

fof(f34,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_145,plain,
    ( k3_xboole_0(sK0,sK1) != X0
    | k2_xboole_0(X0,X1) = X1
    | k1_tarski(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_146,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) = k1_tarski(sK3) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_136,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_137,plain,
    ( r1_tarski(k1_tarski(sK3),sK2) ),
    inference(unflattening,[status(thm)],[c_136])).

cnf(c_150,plain,
    ( k2_xboole_0(X0,X1) = X1
    | k1_tarski(sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_137])).

cnf(c_151,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_389,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_391,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1978,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_389,c_391])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_392,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3255,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1978,c_392])).

cnf(c_10,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4195,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,sK2)) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3255,c_10])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4198,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,sK2)) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_4195,c_9])).

cnf(c_7301,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK3)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_151,c_4198])).

cnf(c_7386,plain,
    ( k3_xboole_0(sK1,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7301,c_3255])).

cnf(c_8201,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,k1_tarski(sK3))) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7386,c_10])).

cnf(c_8214,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,k1_tarski(sK3))) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_8201,c_9])).

cnf(c_27083,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[status(thm)],[c_146,c_8214])).

cnf(c_27220,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27083,c_7386])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_713,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_8])).

cnf(c_1015,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_713])).

cnf(c_28656,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27220,c_1015])).

cnf(c_221,plain,
    ( X0 != X1
    | X2 != X3
    | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_14417,plain,
    ( k3_xboole_0(sK1,sK2) != X0
    | k3_xboole_0(sK1,sK0) != X1
    | k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) = k2_xboole_0(X1,X0) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_14419,plain,
    ( k3_xboole_0(sK1,sK2) != k1_xboole_0
    | k3_xboole_0(sK1,sK0) != k1_xboole_0
    | k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14417])).

cnf(c_220,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4271,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_14416,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) != k2_xboole_0(X0,X1)
    | k1_xboole_0 != k2_xboole_0(X0,X1)
    | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4271])).

cnf(c_14418,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14416])).

cnf(c_490,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != X0
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_2988,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k1_xboole_0
    | k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_1159,plain,
    ( ~ r1_xboole_0(sK1,X0)
    | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2691,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_219,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_741,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_220,c_219])).

cnf(c_2364,plain,
    ( X0 = k2_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_741,c_9])).

cnf(c_2365,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_1177,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_517,plain,
    ( X0 != X1
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != X1
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_671,plain,
    ( X0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = X0
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1176,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | k2_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_513,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_480,plain,
    ( r1_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_6,c_12])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_451,plain,
    ( r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28656,c_14419,c_14418,c_2988,c_2691,c_2365,c_1177,c_1176,c_513,c_480,c_451,c_11])).


%------------------------------------------------------------------------------
