%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:42 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  140 (3907 expanded)
%              Number of clauses        :   92 (1329 expanded)
%              Number of leaves         :   15 ( 923 expanded)
%              Depth                    :   36
%              Number of atoms          :  243 (10169 expanded)
%              Number of equality atoms :  216 (9766 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK3 != sK5
        | sK2 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( sK3 != sK5
      | sK2 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).

fof(f58,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f46,f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f53,f46,f46,f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f60,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,
    ( sK3 != sK5
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_191,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_192,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_799,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_192])).

cnf(c_23,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1118,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_23,c_17])).

cnf(c_16,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1255,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1118,c_16])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1126,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_17,c_0])).

cnf(c_1130,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1126,c_17])).

cnf(c_8645,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_1255,c_1130])).

cnf(c_1121,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_23,c_17])).

cnf(c_1315,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_1121,c_16])).

cnf(c_8840,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_8645,c_23,c_1315])).

cnf(c_8841,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    inference(demodulation,[status(thm)],[c_8840,c_16])).

cnf(c_1124,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17,c_192])).

cnf(c_3834,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_zfmisc_1(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1124])).

cnf(c_10954,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8841,c_3834])).

cnf(c_15,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11067,plain,
    ( k4_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10954,c_15])).

cnf(c_1314,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_1121,c_0])).

cnf(c_1320,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1314,c_1118])).

cnf(c_1321,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
    inference(demodulation,[status(thm)],[c_1320,c_17,c_1118])).

cnf(c_11068,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11067,c_1121,c_1321])).

cnf(c_11293,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_799,c_11068])).

cnf(c_11527,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11293,c_8,c_16,c_23])).

cnf(c_882,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_192,c_0])).

cnf(c_888,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_882,c_8])).

cnf(c_11528,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11527,c_888])).

cnf(c_14,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11659,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11528,c_14])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_755,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_756,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_12080,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11659,c_22,c_31,c_32,c_756])).

cnf(c_1011,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_23,c_16])).

cnf(c_1226,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1011,c_17])).

cnf(c_12087,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) = k2_zfmisc_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12080,c_1226])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_12089,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12087,c_12])).

cnf(c_12204,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12089,c_14])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_753,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_754,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_13129,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12204,c_21,c_31,c_32,c_754])).

cnf(c_6,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13150,plain,
    ( k4_xboole_0(sK2,sK4) != k1_xboole_0
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_13129,c_6])).

cnf(c_1008,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_23,c_16])).

cnf(c_1165,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_1008,c_17])).

cnf(c_2248,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) != k1_xboole_0
    | k4_xboole_0(sK2,sK4) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1165,c_14])).

cnf(c_902,plain,
    ( X0 != X1
    | k4_xboole_0(sK4,sK2) != X1
    | k4_xboole_0(sK4,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_3773,plain,
    ( k4_xboole_0(sK4,sK2) != X0
    | k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_3775,plain,
    ( k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK4,sK2) != k1_xboole_0
    | k4_xboole_0(sK2,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3773])).

cnf(c_784,plain,
    ( k4_xboole_0(sK4,X0) != k4_xboole_0(X0,sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3774,plain,
    ( k4_xboole_0(sK4,sK2) != k4_xboole_0(sK2,sK4)
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_19,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_639,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_841,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_639])).

cnf(c_2249,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_841])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_643,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12888,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2249,c_643])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_641,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12892,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_12888,c_641])).

cnf(c_1164,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)),k2_zfmisc_1(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1008,c_192])).

cnf(c_12894,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12892,c_1164])).

cnf(c_15281,plain,
    ( sK4 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13150,c_21,c_31,c_32,c_754,c_2248,c_3775,c_3774,c_12204,c_12894])).

cnf(c_15343,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_15281,c_1011])).

cnf(c_15356,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(X0,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_15343,c_16])).

cnf(c_15344,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,X0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_15281,c_1008])).

cnf(c_15353,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,X0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_15344,c_16])).

cnf(c_18650,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_15356,c_15353])).

cnf(c_18651,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_18650,c_15356])).

cnf(c_18653,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18651,c_12,c_799,c_15353])).

cnf(c_18859,plain,
    ( k4_xboole_0(sK5,sK3) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18653,c_14])).

cnf(c_20360,plain,
    ( k4_xboole_0(sK5,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18859,c_22,c_31,c_32,c_756])).

cnf(c_20390,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20360,c_0])).

cnf(c_20439,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_20390,c_12080])).

cnf(c_20440,plain,
    ( sK5 = sK3 ),
    inference(demodulation,[status(thm)],[c_20439,c_8])).

cnf(c_20,negated_conjecture,
    ( sK2 != sK4
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15345,plain,
    ( sK2 != sK2
    | sK5 != sK3 ),
    inference(demodulation,[status(thm)],[c_15281,c_20])).

cnf(c_15349,plain,
    ( sK5 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_15345])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20440,c_15349])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.32/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.51  
% 7.32/1.51  ------  iProver source info
% 7.32/1.51  
% 7.32/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.51  git: non_committed_changes: false
% 7.32/1.51  git: last_make_outside_of_git: false
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     num_symb
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       true
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  ------ Parsing...
% 7.32/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.51  ------ Proving...
% 7.32/1.51  ------ Problem Properties 
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  clauses                                 23
% 7.32/1.51  conjectures                             4
% 7.32/1.51  EPR                                     4
% 7.32/1.51  Horn                                    20
% 7.32/1.51  unary                                   12
% 7.32/1.51  binary                                  10
% 7.32/1.51  lits                                    35
% 7.32/1.51  lits eq                                 21
% 7.32/1.51  fd_pure                                 0
% 7.32/1.51  fd_pseudo                               0
% 7.32/1.51  fd_cond                                 2
% 7.32/1.51  fd_pseudo_cond                          1
% 7.32/1.51  AC symbols                              0
% 7.32/1.51  
% 7.32/1.51  ------ Schedule dynamic 5 is on 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ 
% 7.32/1.51  Current options:
% 7.32/1.51  ------ 
% 7.32/1.51  
% 7.32/1.51  ------ Input Options
% 7.32/1.51  
% 7.32/1.51  --out_options                           all
% 7.32/1.51  --tptp_safe_out                         true
% 7.32/1.51  --problem_path                          ""
% 7.32/1.51  --include_path                          ""
% 7.32/1.51  --clausifier                            res/vclausify_rel
% 7.32/1.51  --clausifier_options                    --mode clausify
% 7.32/1.51  --stdin                                 false
% 7.32/1.51  --stats_out                             all
% 7.32/1.51  
% 7.32/1.51  ------ General Options
% 7.32/1.51  
% 7.32/1.51  --fof                                   false
% 7.32/1.51  --time_out_real                         305.
% 7.32/1.51  --time_out_virtual                      -1.
% 7.32/1.51  --symbol_type_check                     false
% 7.32/1.51  --clausify_out                          false
% 7.32/1.51  --sig_cnt_out                           false
% 7.32/1.51  --trig_cnt_out                          false
% 7.32/1.51  --trig_cnt_out_tolerance                1.
% 7.32/1.51  --trig_cnt_out_sk_spl                   false
% 7.32/1.51  --abstr_cl_out                          false
% 7.32/1.51  
% 7.32/1.51  ------ Global Options
% 7.32/1.51  
% 7.32/1.51  --schedule                              default
% 7.32/1.51  --add_important_lit                     false
% 7.32/1.51  --prop_solver_per_cl                    1000
% 7.32/1.51  --min_unsat_core                        false
% 7.32/1.51  --soft_assumptions                      false
% 7.32/1.51  --soft_lemma_size                       3
% 7.32/1.51  --prop_impl_unit_size                   0
% 7.32/1.51  --prop_impl_unit                        []
% 7.32/1.51  --share_sel_clauses                     true
% 7.32/1.51  --reset_solvers                         false
% 7.32/1.51  --bc_imp_inh                            [conj_cone]
% 7.32/1.51  --conj_cone_tolerance                   3.
% 7.32/1.51  --extra_neg_conj                        none
% 7.32/1.51  --large_theory_mode                     true
% 7.32/1.51  --prolific_symb_bound                   200
% 7.32/1.51  --lt_threshold                          2000
% 7.32/1.51  --clause_weak_htbl                      true
% 7.32/1.51  --gc_record_bc_elim                     false
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing Options
% 7.32/1.51  
% 7.32/1.51  --preprocessing_flag                    true
% 7.32/1.51  --time_out_prep_mult                    0.1
% 7.32/1.51  --splitting_mode                        input
% 7.32/1.51  --splitting_grd                         true
% 7.32/1.51  --splitting_cvd                         false
% 7.32/1.51  --splitting_cvd_svl                     false
% 7.32/1.51  --splitting_nvd                         32
% 7.32/1.51  --sub_typing                            true
% 7.32/1.51  --prep_gs_sim                           true
% 7.32/1.51  --prep_unflatten                        true
% 7.32/1.51  --prep_res_sim                          true
% 7.32/1.51  --prep_upred                            true
% 7.32/1.51  --prep_sem_filter                       exhaustive
% 7.32/1.51  --prep_sem_filter_out                   false
% 7.32/1.51  --pred_elim                             true
% 7.32/1.51  --res_sim_input                         true
% 7.32/1.51  --eq_ax_congr_red                       true
% 7.32/1.51  --pure_diseq_elim                       true
% 7.32/1.51  --brand_transform                       false
% 7.32/1.51  --non_eq_to_eq                          false
% 7.32/1.51  --prep_def_merge                        true
% 7.32/1.51  --prep_def_merge_prop_impl              false
% 7.32/1.51  --prep_def_merge_mbd                    true
% 7.32/1.51  --prep_def_merge_tr_red                 false
% 7.32/1.51  --prep_def_merge_tr_cl                  false
% 7.32/1.51  --smt_preprocessing                     true
% 7.32/1.51  --smt_ac_axioms                         fast
% 7.32/1.51  --preprocessed_out                      false
% 7.32/1.51  --preprocessed_stats                    false
% 7.32/1.51  
% 7.32/1.51  ------ Abstraction refinement Options
% 7.32/1.51  
% 7.32/1.51  --abstr_ref                             []
% 7.32/1.51  --abstr_ref_prep                        false
% 7.32/1.51  --abstr_ref_until_sat                   false
% 7.32/1.51  --abstr_ref_sig_restrict                funpre
% 7.32/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.51  --abstr_ref_under                       []
% 7.32/1.51  
% 7.32/1.51  ------ SAT Options
% 7.32/1.51  
% 7.32/1.51  --sat_mode                              false
% 7.32/1.51  --sat_fm_restart_options                ""
% 7.32/1.51  --sat_gr_def                            false
% 7.32/1.51  --sat_epr_types                         true
% 7.32/1.51  --sat_non_cyclic_types                  false
% 7.32/1.51  --sat_finite_models                     false
% 7.32/1.51  --sat_fm_lemmas                         false
% 7.32/1.51  --sat_fm_prep                           false
% 7.32/1.51  --sat_fm_uc_incr                        true
% 7.32/1.51  --sat_out_model                         small
% 7.32/1.51  --sat_out_clauses                       false
% 7.32/1.51  
% 7.32/1.51  ------ QBF Options
% 7.32/1.51  
% 7.32/1.51  --qbf_mode                              false
% 7.32/1.51  --qbf_elim_univ                         false
% 7.32/1.51  --qbf_dom_inst                          none
% 7.32/1.51  --qbf_dom_pre_inst                      false
% 7.32/1.51  --qbf_sk_in                             false
% 7.32/1.51  --qbf_pred_elim                         true
% 7.32/1.51  --qbf_split                             512
% 7.32/1.51  
% 7.32/1.51  ------ BMC1 Options
% 7.32/1.51  
% 7.32/1.51  --bmc1_incremental                      false
% 7.32/1.51  --bmc1_axioms                           reachable_all
% 7.32/1.51  --bmc1_min_bound                        0
% 7.32/1.51  --bmc1_max_bound                        -1
% 7.32/1.51  --bmc1_max_bound_default                -1
% 7.32/1.51  --bmc1_symbol_reachability              true
% 7.32/1.51  --bmc1_property_lemmas                  false
% 7.32/1.51  --bmc1_k_induction                      false
% 7.32/1.51  --bmc1_non_equiv_states                 false
% 7.32/1.51  --bmc1_deadlock                         false
% 7.32/1.51  --bmc1_ucm                              false
% 7.32/1.51  --bmc1_add_unsat_core                   none
% 7.32/1.51  --bmc1_unsat_core_children              false
% 7.32/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.51  --bmc1_out_stat                         full
% 7.32/1.51  --bmc1_ground_init                      false
% 7.32/1.51  --bmc1_pre_inst_next_state              false
% 7.32/1.51  --bmc1_pre_inst_state                   false
% 7.32/1.51  --bmc1_pre_inst_reach_state             false
% 7.32/1.51  --bmc1_out_unsat_core                   false
% 7.32/1.51  --bmc1_aig_witness_out                  false
% 7.32/1.51  --bmc1_verbose                          false
% 7.32/1.51  --bmc1_dump_clauses_tptp                false
% 7.32/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.51  --bmc1_dump_file                        -
% 7.32/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.51  --bmc1_ucm_extend_mode                  1
% 7.32/1.51  --bmc1_ucm_init_mode                    2
% 7.32/1.51  --bmc1_ucm_cone_mode                    none
% 7.32/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.51  --bmc1_ucm_relax_model                  4
% 7.32/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.51  --bmc1_ucm_layered_model                none
% 7.32/1.51  --bmc1_ucm_max_lemma_size               10
% 7.32/1.51  
% 7.32/1.51  ------ AIG Options
% 7.32/1.51  
% 7.32/1.51  --aig_mode                              false
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation Options
% 7.32/1.51  
% 7.32/1.51  --instantiation_flag                    true
% 7.32/1.51  --inst_sos_flag                         false
% 7.32/1.51  --inst_sos_phase                        true
% 7.32/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.51  --inst_lit_sel_side                     none
% 7.32/1.51  --inst_solver_per_active                1400
% 7.32/1.51  --inst_solver_calls_frac                1.
% 7.32/1.51  --inst_passive_queue_type               priority_queues
% 7.32/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.51  --inst_passive_queues_freq              [25;2]
% 7.32/1.51  --inst_dismatching                      true
% 7.32/1.51  --inst_eager_unprocessed_to_passive     true
% 7.32/1.51  --inst_prop_sim_given                   true
% 7.32/1.51  --inst_prop_sim_new                     false
% 7.32/1.51  --inst_subs_new                         false
% 7.32/1.51  --inst_eq_res_simp                      false
% 7.32/1.51  --inst_subs_given                       false
% 7.32/1.51  --inst_orphan_elimination               true
% 7.32/1.51  --inst_learning_loop_flag               true
% 7.32/1.51  --inst_learning_start                   3000
% 7.32/1.51  --inst_learning_factor                  2
% 7.32/1.51  --inst_start_prop_sim_after_learn       3
% 7.32/1.51  --inst_sel_renew                        solver
% 7.32/1.51  --inst_lit_activity_flag                true
% 7.32/1.51  --inst_restr_to_given                   false
% 7.32/1.51  --inst_activity_threshold               500
% 7.32/1.51  --inst_out_proof                        true
% 7.32/1.51  
% 7.32/1.51  ------ Resolution Options
% 7.32/1.51  
% 7.32/1.51  --resolution_flag                       false
% 7.32/1.51  --res_lit_sel                           adaptive
% 7.32/1.51  --res_lit_sel_side                      none
% 7.32/1.51  --res_ordering                          kbo
% 7.32/1.51  --res_to_prop_solver                    active
% 7.32/1.51  --res_prop_simpl_new                    false
% 7.32/1.51  --res_prop_simpl_given                  true
% 7.32/1.51  --res_passive_queue_type                priority_queues
% 7.32/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.51  --res_passive_queues_freq               [15;5]
% 7.32/1.51  --res_forward_subs                      full
% 7.32/1.51  --res_backward_subs                     full
% 7.32/1.51  --res_forward_subs_resolution           true
% 7.32/1.51  --res_backward_subs_resolution          true
% 7.32/1.51  --res_orphan_elimination                true
% 7.32/1.51  --res_time_limit                        2.
% 7.32/1.51  --res_out_proof                         true
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Options
% 7.32/1.51  
% 7.32/1.51  --superposition_flag                    true
% 7.32/1.51  --sup_passive_queue_type                priority_queues
% 7.32/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.51  --demod_completeness_check              fast
% 7.32/1.51  --demod_use_ground                      true
% 7.32/1.51  --sup_to_prop_solver                    passive
% 7.32/1.51  --sup_prop_simpl_new                    true
% 7.32/1.51  --sup_prop_simpl_given                  true
% 7.32/1.51  --sup_fun_splitting                     false
% 7.32/1.51  --sup_smt_interval                      50000
% 7.32/1.51  
% 7.32/1.51  ------ Superposition Simplification Setup
% 7.32/1.51  
% 7.32/1.51  --sup_indices_passive                   []
% 7.32/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_full_bw                           [BwDemod]
% 7.32/1.51  --sup_immed_triv                        [TrivRules]
% 7.32/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_immed_bw_main                     []
% 7.32/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.51  
% 7.32/1.51  ------ Combination Options
% 7.32/1.51  
% 7.32/1.51  --comb_res_mult                         3
% 7.32/1.51  --comb_sup_mult                         2
% 7.32/1.51  --comb_inst_mult                        10
% 7.32/1.51  
% 7.32/1.51  ------ Debug Options
% 7.32/1.51  
% 7.32/1.51  --dbg_backtrace                         false
% 7.32/1.51  --dbg_dump_prop_clauses                 false
% 7.32/1.51  --dbg_dump_prop_clauses_file            -
% 7.32/1.51  --dbg_out_stat                          false
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  ------ Proving...
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS status Theorem for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  fof(f8,axiom,(
% 7.32/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f45,plain,(
% 7.32/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.32/1.51    inference(cnf_transformation,[],[f8])).
% 7.32/1.51  
% 7.32/1.51  fof(f5,axiom,(
% 7.32/1.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f19,plain,(
% 7.32/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 7.32/1.51    inference(unused_predicate_definition_removal,[],[f5])).
% 7.32/1.51  
% 7.32/1.51  fof(f23,plain,(
% 7.32/1.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(ennf_transformation,[],[f19])).
% 7.32/1.51  
% 7.32/1.51  fof(f42,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f23])).
% 7.32/1.51  
% 7.32/1.51  fof(f7,axiom,(
% 7.32/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f44,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f7])).
% 7.32/1.51  
% 7.32/1.51  fof(f16,conjecture,(
% 7.32/1.51    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f17,negated_conjecture,(
% 7.32/1.51    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.32/1.51    inference(negated_conjecture,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f26,plain,(
% 7.32/1.51    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.32/1.51    inference(ennf_transformation,[],[f17])).
% 7.32/1.51  
% 7.32/1.51  fof(f27,plain,(
% 7.32/1.51    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 7.32/1.51    inference(flattening,[],[f26])).
% 7.32/1.51  
% 7.32/1.51  fof(f35,plain,(
% 7.32/1.51    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f36,plain,(
% 7.32/1.51    (sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f27,f35])).
% 7.32/1.51  
% 7.32/1.51  fof(f58,plain,(
% 7.32/1.51    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  fof(f14,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f54,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f14])).
% 7.32/1.51  
% 7.32/1.51  fof(f55,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f14])).
% 7.32/1.51  
% 7.32/1.51  fof(f1,axiom,(
% 7.32/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f37,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f1])).
% 7.32/1.51  
% 7.32/1.51  fof(f9,axiom,(
% 7.32/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f46,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f9])).
% 7.32/1.51  
% 7.32/1.51  fof(f62,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.32/1.51    inference(definition_unfolding,[],[f37,f46,f46])).
% 7.32/1.51  
% 7.32/1.51  fof(f13,axiom,(
% 7.32/1.51    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f53,plain,(
% 7.32/1.51    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f13])).
% 7.32/1.51  
% 7.32/1.51  fof(f65,plain,(
% 7.32/1.51    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 7.32/1.51    inference(definition_unfolding,[],[f53,f46,f46,f46])).
% 7.32/1.51  
% 7.32/1.51  fof(f12,axiom,(
% 7.32/1.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f33,plain,(
% 7.32/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.32/1.51    inference(nnf_transformation,[],[f12])).
% 7.32/1.51  
% 7.32/1.51  fof(f34,plain,(
% 7.32/1.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.32/1.51    inference(flattening,[],[f33])).
% 7.32/1.51  
% 7.32/1.51  fof(f50,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f34])).
% 7.32/1.51  
% 7.32/1.51  fof(f59,plain,(
% 7.32/1.51    k1_xboole_0 != sK2),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  fof(f51,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.32/1.51    inference(cnf_transformation,[],[f34])).
% 7.32/1.51  
% 7.32/1.51  fof(f67,plain,(
% 7.32/1.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.32/1.51    inference(equality_resolution,[],[f51])).
% 7.32/1.51  
% 7.32/1.51  fof(f52,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.32/1.51    inference(cnf_transformation,[],[f34])).
% 7.32/1.51  
% 7.32/1.51  fof(f66,plain,(
% 7.32/1.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.32/1.51    inference(equality_resolution,[],[f52])).
% 7.32/1.51  
% 7.32/1.51  fof(f60,plain,(
% 7.32/1.51    k1_xboole_0 != sK3),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  fof(f6,axiom,(
% 7.32/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f24,plain,(
% 7.32/1.51    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 7.32/1.51    inference(ennf_transformation,[],[f6])).
% 7.32/1.51  
% 7.32/1.51  fof(f43,plain,(
% 7.32/1.51    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f24])).
% 7.32/1.51  
% 7.32/1.51  fof(f15,axiom,(
% 7.32/1.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f25,plain,(
% 7.32/1.51    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(ennf_transformation,[],[f15])).
% 7.32/1.51  
% 7.32/1.51  fof(f56,plain,(
% 7.32/1.51    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f10,axiom,(
% 7.32/1.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f47,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f10])).
% 7.32/1.51  
% 7.32/1.51  fof(f11,axiom,(
% 7.32/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.32/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f32,plain,(
% 7.32/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.32/1.51    inference(nnf_transformation,[],[f11])).
% 7.32/1.51  
% 7.32/1.51  fof(f48,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f32])).
% 7.32/1.51  
% 7.32/1.51  fof(f61,plain,(
% 7.32/1.51    sK3 != sK5 | sK2 != sK4),
% 7.32/1.51    inference(cnf_transformation,[],[f36])).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8,plain,
% 7.32/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7,plain,
% 7.32/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_191,plain,
% 7.32/1.51      ( X0 != X1
% 7.32/1.51      | k4_xboole_0(X0,X2) != X3
% 7.32/1.51      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 7.32/1.51      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_192,plain,
% 7.32/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.32/1.51      inference(unflattening,[status(thm)],[c_191]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_799,plain,
% 7.32/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_8,c_192]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_23,negated_conjecture,
% 7.32/1.51      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
% 7.32/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1118,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_23,c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_16,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1255,plain,
% 7.32/1.51      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1118,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_0,plain,
% 7.32/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1126,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_17,c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1130,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_1126,c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8645,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1255,c_1130]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1121,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_23,c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1315,plain,
% 7.32/1.51      ( k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1121,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8840,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_8645,c_23,c_1315]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8841,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_8840,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1124,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_17,c_192]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3834,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_zfmisc_1(X1,X2)) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_0,c_1124]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10954,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_8841,c_3834]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15,plain,
% 7.32/1.51      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11067,plain,
% 7.32/1.51      ( k4_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_10954,c_15]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1314,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1121,c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1320,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_1314,c_1118]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1321,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_1320,c_17,c_1118]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11068,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 7.32/1.51      inference(light_normalisation,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_11067,c_1121,c_1321]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11293,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_799,c_11068]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11527,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_11293,c_8,c_16,c_23]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_882,plain,
% 7.32/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_192,c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_888,plain,
% 7.32/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_882,c_8]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11528,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_11527,c_888]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_14,plain,
% 7.32/1.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.32/1.51      | k1_xboole_0 = X0
% 7.32/1.51      | k1_xboole_0 = X1 ),
% 7.32/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11659,plain,
% 7.32/1.51      ( k4_xboole_0(sK3,sK5) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_11528,c_14]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_22,negated_conjecture,
% 7.32/1.51      ( k1_xboole_0 != sK2 ),
% 7.32/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_31,plain,
% 7.32/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.32/1.51      | k1_xboole_0 = k1_xboole_0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_13,plain,
% 7.32/1.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_32,plain,
% 7.32/1.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_755,plain,
% 7.32/1.51      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_363]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_756,plain,
% 7.32/1.51      ( sK2 != k1_xboole_0
% 7.32/1.51      | k1_xboole_0 = sK2
% 7.32/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_755]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12080,plain,
% 7.32/1.51      ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_11659,c_22,c_31,c_32,c_756]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1011,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(X0,sK5)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_23,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1226,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1011,c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12087,plain,
% 7.32/1.51      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) = k2_zfmisc_1(sK4,k1_xboole_0) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_12080,c_1226]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12,plain,
% 7.32/1.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12089,plain,
% 7.32/1.51      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_12087,c_12]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12204,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_12089,c_14]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_21,negated_conjecture,
% 7.32/1.51      ( k1_xboole_0 != sK3 ),
% 7.32/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_753,plain,
% 7.32/1.51      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_363]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_754,plain,
% 7.32/1.51      ( sK3 != k1_xboole_0
% 7.32/1.51      | k1_xboole_0 = sK3
% 7.32/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_753]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_13129,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_12204,c_21,c_31,c_32,c_754]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_6,plain,
% 7.32/1.51      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_13150,plain,
% 7.32/1.51      ( k4_xboole_0(sK2,sK4) != k1_xboole_0 | sK4 = sK2 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_13129,c_6]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1008,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_23,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1165,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK3) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1008,c_17]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2248,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) != k1_xboole_0
% 7.32/1.51      | k4_xboole_0(sK2,sK4) = k1_xboole_0
% 7.32/1.51      | sK3 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1165,c_14]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_902,plain,
% 7.32/1.51      ( X0 != X1
% 7.32/1.51      | k4_xboole_0(sK4,sK2) != X1
% 7.32/1.51      | k4_xboole_0(sK4,sK2) = X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_363]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3773,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,sK2) != X0
% 7.32/1.51      | k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,sK4)
% 7.32/1.51      | k4_xboole_0(sK2,sK4) != X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_902]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3775,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,sK4)
% 7.32/1.51      | k4_xboole_0(sK4,sK2) != k1_xboole_0
% 7.32/1.51      | k4_xboole_0(sK2,sK4) != k1_xboole_0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_3773]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_784,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,X0) != k4_xboole_0(X0,sK4) | sK4 = X0 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3774,plain,
% 7.32/1.51      ( k4_xboole_0(sK4,sK2) != k4_xboole_0(sK2,sK4) | sK4 = sK2 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_784]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_19,plain,
% 7.32/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.32/1.51      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_639,plain,
% 7.32/1.51      ( r1_xboole_0(X0,X1) != iProver_top
% 7.32/1.51      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_841,plain,
% 7.32/1.51      ( r1_xboole_0(X0,sK4) != iProver_top
% 7.32/1.51      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_23,c_639]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2249,plain,
% 7.32/1.51      ( r1_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 7.32/1.51      | r1_xboole_0(k4_xboole_0(sK2,sK4),sK4) != iProver_top ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1165,c_841]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9,plain,
% 7.32/1.51      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_643,plain,
% 7.32/1.51      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12888,plain,
% 7.32/1.51      ( r1_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 7.32/1.51      inference(forward_subsumption_resolution,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_2249,c_643]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11,plain,
% 7.32/1.51      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.32/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_641,plain,
% 7.32/1.51      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.32/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12892,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_12888,c_641]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1164,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)),k2_zfmisc_1(sK2,sK3)) = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_1008,c_192]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12894,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_12892,c_1164]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15281,plain,
% 7.32/1.51      ( sK4 = sK2 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_13150,c_21,c_31,c_32,c_754,c_2248,c_3775,c_3774,
% 7.32/1.51                 c_12204,c_12894]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15343,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(X0,sK5)) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_15281,c_1011]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15356,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(X0,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(X0,sK5)) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_15343,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15344,plain,
% 7.32/1.51      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,X0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,X0)) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_15281,c_1008]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15353,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,X0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,X0)) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_15344,c_16]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18650,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_15356,c_15353]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18651,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK3)) ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_18650,c_15356]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18653,plain,
% 7.32/1.51      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_18651,c_12,c_799,c_15353]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18859,plain,
% 7.32/1.51      ( k4_xboole_0(sK5,sK3) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_18653,c_14]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20360,plain,
% 7.32/1.51      ( k4_xboole_0(sK5,sK3) = k1_xboole_0 ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_18859,c_22,c_31,c_32,c_756]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20390,plain,
% 7.32/1.51      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
% 7.32/1.51      inference(superposition,[status(thm)],[c_20360,c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20439,plain,
% 7.32/1.51      ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
% 7.32/1.51      inference(light_normalisation,[status(thm)],[c_20390,c_12080]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20440,plain,
% 7.32/1.51      ( sK5 = sK3 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_20439,c_8]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_20,negated_conjecture,
% 7.32/1.51      ( sK2 != sK4 | sK3 != sK5 ),
% 7.32/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15345,plain,
% 7.32/1.51      ( sK2 != sK2 | sK5 != sK3 ),
% 7.32/1.51      inference(demodulation,[status(thm)],[c_15281,c_20]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15349,plain,
% 7.32/1.51      ( sK5 != sK3 ),
% 7.32/1.51      inference(equality_resolution_simp,[status(thm)],[c_15345]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(contradiction,plain,
% 7.32/1.51      ( $false ),
% 7.32/1.51      inference(minisat,[status(thm)],[c_20440,c_15349]) ).
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  ------                               Statistics
% 7.32/1.51  
% 7.32/1.51  ------ General
% 7.32/1.51  
% 7.32/1.51  abstr_ref_over_cycles:                  0
% 7.32/1.51  abstr_ref_under_cycles:                 0
% 7.32/1.51  gc_basic_clause_elim:                   0
% 7.32/1.51  forced_gc_time:                         0
% 7.32/1.51  parsing_time:                           0.014
% 7.32/1.51  unif_index_cands_time:                  0.
% 7.32/1.51  unif_index_add_time:                    0.
% 7.32/1.51  orderings_time:                         0.
% 7.32/1.51  out_proof_time:                         0.014
% 7.32/1.51  total_time:                             0.662
% 7.32/1.51  num_of_symbols:                         43
% 7.32/1.51  num_of_terms:                           29758
% 7.32/1.51  
% 7.32/1.51  ------ Preprocessing
% 7.32/1.51  
% 7.32/1.51  num_of_splits:                          0
% 7.32/1.51  num_of_split_atoms:                     0
% 7.32/1.51  num_of_reused_defs:                     0
% 7.32/1.51  num_eq_ax_congr_red:                    10
% 7.32/1.51  num_of_sem_filtered_clauses:            1
% 7.32/1.51  num_of_subtypes:                        0
% 7.32/1.51  monotx_restored_types:                  0
% 7.32/1.51  sat_num_of_epr_types:                   0
% 7.32/1.51  sat_num_of_non_cyclic_types:            0
% 7.32/1.51  sat_guarded_non_collapsed_types:        0
% 7.32/1.51  num_pure_diseq_elim:                    0
% 7.32/1.51  simp_replaced_by:                       0
% 7.32/1.51  res_preprocessed:                       106
% 7.32/1.51  prep_upred:                             0
% 7.32/1.51  prep_unflattend:                        8
% 7.32/1.51  smt_new_axioms:                         0
% 7.32/1.51  pred_elim_cands:                        2
% 7.32/1.51  pred_elim:                              1
% 7.32/1.51  pred_elim_cl:                           1
% 7.32/1.51  pred_elim_cycles:                       3
% 7.32/1.51  merged_defs:                            8
% 7.32/1.51  merged_defs_ncl:                        0
% 7.32/1.51  bin_hyper_res:                          8
% 7.32/1.51  prep_cycles:                            4
% 7.32/1.51  pred_elim_time:                         0.002
% 7.32/1.51  splitting_time:                         0.
% 7.32/1.51  sem_filter_time:                        0.
% 7.32/1.51  monotx_time:                            0.001
% 7.32/1.51  subtype_inf_time:                       0.
% 7.32/1.51  
% 7.32/1.51  ------ Problem properties
% 7.32/1.51  
% 7.32/1.51  clauses:                                23
% 7.32/1.51  conjectures:                            4
% 7.32/1.51  epr:                                    4
% 7.32/1.51  horn:                                   20
% 7.32/1.51  ground:                                 4
% 7.32/1.51  unary:                                  12
% 7.32/1.51  binary:                                 10
% 7.32/1.51  lits:                                   35
% 7.32/1.51  lits_eq:                                21
% 7.32/1.51  fd_pure:                                0
% 7.32/1.51  fd_pseudo:                              0
% 7.32/1.51  fd_cond:                                2
% 7.32/1.51  fd_pseudo_cond:                         1
% 7.32/1.51  ac_symbols:                             0
% 7.32/1.51  
% 7.32/1.51  ------ Propositional Solver
% 7.32/1.51  
% 7.32/1.51  prop_solver_calls:                      31
% 7.32/1.51  prop_fast_solver_calls:                 688
% 7.32/1.51  smt_solver_calls:                       0
% 7.32/1.51  smt_fast_solver_calls:                  0
% 7.32/1.51  prop_num_of_clauses:                    6409
% 7.32/1.51  prop_preprocess_simplified:             11257
% 7.32/1.51  prop_fo_subsumed:                       13
% 7.32/1.51  prop_solver_time:                       0.
% 7.32/1.51  smt_solver_time:                        0.
% 7.32/1.51  smt_fast_solver_time:                   0.
% 7.32/1.51  prop_fast_solver_time:                  0.
% 7.32/1.51  prop_unsat_core_time:                   0.
% 7.32/1.51  
% 7.32/1.51  ------ QBF
% 7.32/1.51  
% 7.32/1.51  qbf_q_res:                              0
% 7.32/1.51  qbf_num_tautologies:                    0
% 7.32/1.51  qbf_prep_cycles:                        0
% 7.32/1.51  
% 7.32/1.51  ------ BMC1
% 7.32/1.51  
% 7.32/1.51  bmc1_current_bound:                     -1
% 7.32/1.51  bmc1_last_solved_bound:                 -1
% 7.32/1.51  bmc1_unsat_core_size:                   -1
% 7.32/1.51  bmc1_unsat_core_parents_size:           -1
% 7.32/1.51  bmc1_merge_next_fun:                    0
% 7.32/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.51  
% 7.32/1.51  ------ Instantiation
% 7.32/1.51  
% 7.32/1.51  inst_num_of_clauses:                    2423
% 7.32/1.51  inst_num_in_passive:                    1314
% 7.32/1.51  inst_num_in_active:                     775
% 7.32/1.51  inst_num_in_unprocessed:                334
% 7.32/1.51  inst_num_of_loops:                      810
% 7.32/1.51  inst_num_of_learning_restarts:          0
% 7.32/1.51  inst_num_moves_active_passive:          33
% 7.32/1.51  inst_lit_activity:                      0
% 7.32/1.51  inst_lit_activity_moves:                0
% 7.32/1.51  inst_num_tautologies:                   0
% 7.32/1.51  inst_num_prop_implied:                  0
% 7.32/1.51  inst_num_existing_simplified:           0
% 7.32/1.51  inst_num_eq_res_simplified:             0
% 7.32/1.51  inst_num_child_elim:                    0
% 7.32/1.51  inst_num_of_dismatching_blockings:      638
% 7.32/1.51  inst_num_of_non_proper_insts:           2080
% 7.32/1.51  inst_num_of_duplicates:                 0
% 7.32/1.51  inst_inst_num_from_inst_to_res:         0
% 7.32/1.51  inst_dismatching_checking_time:         0.
% 7.32/1.51  
% 7.32/1.51  ------ Resolution
% 7.32/1.51  
% 7.32/1.51  res_num_of_clauses:                     0
% 7.32/1.51  res_num_in_passive:                     0
% 7.32/1.51  res_num_in_active:                      0
% 7.32/1.51  res_num_of_loops:                       110
% 7.32/1.51  res_forward_subset_subsumed:            183
% 7.32/1.51  res_backward_subset_subsumed:           2
% 7.32/1.51  res_forward_subsumed:                   0
% 7.32/1.51  res_backward_subsumed:                  0
% 7.32/1.51  res_forward_subsumption_resolution:     0
% 7.32/1.51  res_backward_subsumption_resolution:    0
% 7.32/1.51  res_clause_to_clause_subsumption:       6415
% 7.32/1.51  res_orphan_elimination:                 0
% 7.32/1.51  res_tautology_del:                      125
% 7.32/1.51  res_num_eq_res_simplified:              0
% 7.32/1.51  res_num_sel_changes:                    0
% 7.32/1.51  res_moves_from_active_to_pass:          0
% 7.32/1.51  
% 7.32/1.51  ------ Superposition
% 7.32/1.51  
% 7.32/1.51  sup_time_total:                         0.
% 7.32/1.51  sup_time_generating:                    0.
% 7.32/1.51  sup_time_sim_full:                      0.
% 7.32/1.51  sup_time_sim_immed:                     0.
% 7.32/1.51  
% 7.32/1.51  sup_num_of_clauses:                     1102
% 7.32/1.51  sup_num_in_active:                      77
% 7.32/1.51  sup_num_in_passive:                     1025
% 7.32/1.51  sup_num_of_loops:                       161
% 7.32/1.51  sup_fw_superposition:                   1844
% 7.32/1.51  sup_bw_superposition:                   1491
% 7.32/1.51  sup_immediate_simplified:               1927
% 7.32/1.51  sup_given_eliminated:                   6
% 7.32/1.51  comparisons_done:                       0
% 7.32/1.51  comparisons_avoided:                    0
% 7.32/1.51  
% 7.32/1.51  ------ Simplifications
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  sim_fw_subset_subsumed:                 15
% 7.32/1.51  sim_bw_subset_subsumed:                 10
% 7.32/1.51  sim_fw_subsumed:                        472
% 7.32/1.51  sim_bw_subsumed:                        75
% 7.32/1.51  sim_fw_subsumption_res:                 1
% 7.32/1.51  sim_bw_subsumption_res:                 0
% 7.32/1.51  sim_tautology_del:                      44
% 7.32/1.51  sim_eq_tautology_del:                   350
% 7.32/1.51  sim_eq_res_simp:                        2
% 7.32/1.51  sim_fw_demodulated:                     1522
% 7.32/1.51  sim_bw_demodulated:                     112
% 7.32/1.51  sim_light_normalised:                   647
% 7.32/1.51  sim_joinable_taut:                      0
% 7.32/1.51  sim_joinable_simp:                      0
% 7.32/1.51  sim_ac_normalised:                      0
% 7.32/1.51  sim_smt_subsumption:                    0
% 7.32/1.51  
%------------------------------------------------------------------------------
