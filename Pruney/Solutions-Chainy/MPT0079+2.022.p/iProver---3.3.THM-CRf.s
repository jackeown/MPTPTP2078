%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:49 EST 2020

% Result     : Theorem 28.00s
% Output     : CNFRefutation 28.00s
% Verified   : 
% Statistics : Number of formulae       :  439 (730726 expanded)
%              Number of clauses        :  389 (299267 expanded)
%              Number of leaves         :   20 (184049 expanded)
%              Depth                    :   59
%              Number of atoms          :  494 (1100409 expanded)
%              Number of equality atoms :  440 (860329 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK3 != sK4
      & r1_xboole_0(sK5,sK3)
      & r1_xboole_0(sK4,sK2)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK3 != sK4
    & r1_xboole_0(sK5,sK3)
    & r1_xboole_0(sK4,sK2)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f27])).

fof(f44,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f42,f42])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f45,plain,(
    r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_243,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_516,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_243])).

cnf(c_2036,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_516])).

cnf(c_244,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_991,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_244])).

cnf(c_2104,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2036,c_8,c_991])).

cnf(c_17,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_153,negated_conjecture,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
    inference(theory_normalisation,[status(thm)],[c_17,c_13,c_0])).

cnf(c_992,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_153,c_244])).

cnf(c_1280,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_992])).

cnf(c_11960,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK3),sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_2104,c_1280])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_990,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_244])).

cnf(c_11,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_238,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_1078,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_238])).

cnf(c_1079,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1078,c_8])).

cnf(c_1856,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_992,c_1079])).

cnf(c_3361,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k1_xboole_0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_990,c_1856])).

cnf(c_3375,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3361,c_6])).

cnf(c_1075,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_29572,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3375,c_1075])).

cnf(c_29985,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK4,sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_29572,c_6])).

cnf(c_1177,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_13])).

cnf(c_518,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_153,c_243])).

cnf(c_691,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_518,c_243])).

cnf(c_3904,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1177,c_691])).

cnf(c_1282,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_2,c_992])).

cnf(c_1344,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1282,c_243])).

cnf(c_3927,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3904,c_153,c_1344])).

cnf(c_10,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4237,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_3927,c_10])).

cnf(c_29570,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(sK4,sK2))) ),
    inference(superposition,[status(thm)],[c_4237,c_1075])).

cnf(c_29988,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_29570,c_1075])).

cnf(c_571,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_2208,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_153,c_571])).

cnf(c_29989,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_29988,c_2208])).

cnf(c_566,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_243])).

cnf(c_30212,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k2_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_29989,c_566])).

cnf(c_30236,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_30212,c_153])).

cnf(c_1012,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_244,c_518])).

cnf(c_1014,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1012,c_691])).

cnf(c_30237,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_30236,c_2,c_566,c_1014])).

cnf(c_30405,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_30237,c_571])).

cnf(c_30488,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_30405,c_2208])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1095,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_12])).

cnf(c_30532,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) ),
    inference(superposition,[status(thm)],[c_30488,c_1095])).

cnf(c_30196,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_29989,c_10])).

cnf(c_628,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_30521,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) ),
    inference(superposition,[status(thm)],[c_30488,c_628])).

cnf(c_30554,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_30521,c_30488])).

cnf(c_30199,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_29989,c_516])).

cnf(c_30202,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_29989,c_991])).

cnf(c_30239,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k2_xboole_0(sK2,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_30202,c_991])).

cnf(c_30240,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_30199,c_29989,c_30239])).

cnf(c_30555,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_30554,c_30240])).

cnf(c_2226,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_571,c_1])).

cnf(c_573,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_1834,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1079])).

cnf(c_2231,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2226,c_9,c_573,c_1834])).

cnf(c_2716,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2231,c_11])).

cnf(c_29759,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X3,X0),k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1075,c_2716])).

cnf(c_29787,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_29759,c_2716])).

cnf(c_30556,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_30555,c_29787])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_237,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_105,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_106,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
    inference(unflattening,[status(thm)],[c_105])).

cnf(c_234,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_9948,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_237,c_234])).

cnf(c_30557,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_30556,c_9948])).

cnf(c_30558,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_30557,c_6])).

cnf(c_30659,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_30532,c_30196,c_30558])).

cnf(c_12870,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_8,c_2716])).

cnf(c_12989,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_12870,c_2716])).

cnf(c_30660,plain,
    ( k4_xboole_0(sK4,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_30659,c_2231,c_12989])).

cnf(c_31360,plain,
    ( k2_xboole_0(sK3,sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_29985,c_29985,c_30660])).

cnf(c_31374,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_31360,c_13])).

cnf(c_576,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_243,c_10])).

cnf(c_6691,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(X0,k2_xboole_0(sK4,X1))) = k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK4,X1))) ),
    inference(superposition,[status(thm)],[c_992,c_576])).

cnf(c_33675,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))) = k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_31374,c_6691])).

cnf(c_33721,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_33675,c_31374])).

cnf(c_33722,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),sK3) = k4_xboole_0(sK5,sK3) ),
    inference(light_normalisation,[status(thm)],[c_33721,c_31360])).

cnf(c_245,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_2211,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_245,c_571])).

cnf(c_33723,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_33722,c_571,c_1177,c_2211])).

cnf(c_33616,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_518,c_31374])).

cnf(c_1296,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_992,c_244])).

cnf(c_11211,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1296,c_1296])).

cnf(c_1766,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_245,c_992])).

cnf(c_994,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_518,c_244])).

cnf(c_695,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_518,c_243])).

cnf(c_9418,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,sK5))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_994,c_695])).

cnf(c_9447,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) = k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) ),
    inference(superposition,[status(thm)],[c_994,c_245])).

cnf(c_682,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_518])).

cnf(c_2911,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_682,c_990])).

cnf(c_2930,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_990,c_13])).

cnf(c_989,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_244])).

cnf(c_2771,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_989,c_13])).

cnf(c_2800,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_2771,c_13])).

cnf(c_2801,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2800,c_1177])).

cnf(c_2961,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_2930,c_2801])).

cnf(c_2962,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2961,c_990,c_2801])).

cnf(c_2983,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_2911,c_2962])).

cnf(c_2984,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_2983,c_1766])).

cnf(c_3670,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X0)),X3)) = k2_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_566,c_245])).

cnf(c_1715,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_245])).

cnf(c_3697,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_3670,c_1715,c_2801])).

cnf(c_9490,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) ),
    inference(demodulation,[status(thm)],[c_9447,c_2984,c_3697])).

cnf(c_9518,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_9418,c_9490])).

cnf(c_2751,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(superposition,[status(thm)],[c_518,c_989])).

cnf(c_2823,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_2751,c_2801])).

cnf(c_1343,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_1282,c_243])).

cnf(c_1013,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_244,c_682])).

cnf(c_1345,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1343,c_1013])).

cnf(c_1765,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_245,c_1280])).

cnf(c_2824,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2823,c_1345,c_1765])).

cnf(c_3051,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1766,c_516])).

cnf(c_855,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2,c_691])).

cnf(c_865,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_855,c_153])).

cnf(c_869,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK5,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_865,c_243])).

cnf(c_2948,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_990,c_869])).

cnf(c_2955,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_2948,c_990])).

cnf(c_3055,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3051,c_153,c_2955])).

cnf(c_9519,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9518,c_2824,c_3055])).

cnf(c_11227,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11211,c_153,c_1766,c_9519])).

cnf(c_12172,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_243,c_11227])).

cnf(c_24700,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_1177,c_12172])).

cnf(c_24925,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24700,c_1014,c_11227])).

cnf(c_34371,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_33616,c_24925])).

cnf(c_12158,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_516,c_11227])).

cnf(c_868,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK5,sK2)) ),
    inference(superposition,[status(thm)],[c_865,c_10])).

cnf(c_1476,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),k4_xboole_0(sK3,k2_xboole_0(sK5,sK2))) = k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_868,c_8])).

cnf(c_1001,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_865,c_244])).

cnf(c_1477,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_1476,c_8,c_1001,c_1014])).

cnf(c_1478,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),sK3) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1477,c_2])).

cnf(c_4093,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1478,c_13])).

cnf(c_1864,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1079,c_8])).

cnf(c_1867,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1864,c_6])).

cnf(c_7971,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK5,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4093,c_1867])).

cnf(c_8008,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_7971,c_4093])).

cnf(c_12267,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_12158,c_8008])).

cnf(c_34372,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_34371,c_12267])).

cnf(c_34373,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_34372,c_1177])).

cnf(c_52452,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_11960,c_11960,c_33723,c_34373])).

cnf(c_52476,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_52452,c_10])).

cnf(c_1838,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_1079])).

cnf(c_29567,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1838,c_1075])).

cnf(c_2203,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_571])).

cnf(c_2242,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2203,c_571])).

cnf(c_29994,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_29567,c_6,c_2242])).

cnf(c_725,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_682,c_243])).

cnf(c_31565,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_29994,c_725])).

cnf(c_31650,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_31565,c_153])).

cnf(c_31904,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_31650,c_243])).

cnf(c_34376,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_31904,c_31904,c_34373])).

cnf(c_34481,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_34376,c_31374])).

cnf(c_34484,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_34481,c_31650,c_34373])).

cnf(c_34828,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_34484,c_989])).

cnf(c_34919,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_34828,c_34484])).

cnf(c_45745,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_34919,c_576])).

cnf(c_1283,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_6,c_992])).

cnf(c_525,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1373,plain,
    ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1283,c_525])).

cnf(c_36635,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1373,c_1373,c_34373])).

cnf(c_36662,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_36635,c_576])).

cnf(c_45759,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_45745,c_36662])).

cnf(c_1843,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_153,c_1079])).

cnf(c_29559,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1843,c_1075])).

cnf(c_30026,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_29559,c_6])).

cnf(c_31709,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k2_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_30026,c_13])).

cnf(c_40132,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_628,c_31709])).

cnf(c_40303,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,sK5) ),
    inference(demodulation,[status(thm)],[c_40132,c_31709])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_96,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_97,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_235,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_620,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_235])).

cnf(c_9949,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_237,c_620])).

cnf(c_40304,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK5) ),
    inference(light_normalisation,[status(thm)],[c_40303,c_9949])).

cnf(c_40305,plain,
    ( k2_xboole_0(sK2,sK5) = sK2 ),
    inference(demodulation,[status(thm)],[c_40304,c_6])).

cnf(c_1486,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_869])).

cnf(c_1505,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1486,c_865])).

cnf(c_1603,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK5,sK2))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1505,c_244])).

cnf(c_1612,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1603,c_865])).

cnf(c_1635,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1612,c_518])).

cnf(c_2464,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_1635,c_571])).

cnf(c_2479,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_2464,c_2208])).

cnf(c_40358,plain,
    ( k4_xboole_0(sK5,sK4) = k4_xboole_0(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_40305,c_2479])).

cnf(c_40542,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_40358,c_12])).

cnf(c_40571,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_40542,c_40358])).

cnf(c_30535,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_30488,c_1])).

cnf(c_30656,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_30535,c_30196,c_30558])).

cnf(c_30657,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30656,c_238,c_12989])).

cnf(c_40572,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_40571,c_30657])).

cnf(c_40573,plain,
    ( k4_xboole_0(sK5,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_40572,c_9])).

cnf(c_41499,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK5,sK2)) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_40573,c_1095])).

cnf(c_29569,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1856,c_1075])).

cnf(c_4975,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1838,c_8])).

cnf(c_4982,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_4975,c_6,c_2801])).

cnf(c_13026,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_516,c_4982])).

cnf(c_2906,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_516,c_990])).

cnf(c_2990,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2906,c_990])).

cnf(c_13289,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_13026,c_10,c_2990])).

cnf(c_19405,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k2_xboole_0(sK2,sK3))) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) ),
    inference(superposition,[status(thm)],[c_4093,c_13289])).

cnf(c_1848,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_1079])).

cnf(c_3290,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,sK5),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_990,c_1848])).

cnf(c_3304,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3290,c_525])).

cnf(c_7974,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_4093,c_990])).

cnf(c_8005,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_7974,c_990,c_2801])).

cnf(c_19653,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_19405,c_3304,c_8005])).

cnf(c_29990,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_29569,c_19653])).

cnf(c_29991,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_29990,c_10,c_2984])).

cnf(c_31576,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_29994,c_1766])).

cnf(c_31629,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_31576,c_1373,c_29991])).

cnf(c_35539,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_29991,c_31629,c_34373])).

cnf(c_2220,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_992,c_571])).

cnf(c_4469,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k4_xboole_0(k2_xboole_0(sK4,k1_xboole_0),sK5) ),
    inference(superposition,[status(thm)],[c_990,c_2220])).

cnf(c_4490,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_4469,c_6])).

cnf(c_35548,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_35539,c_4490])).

cnf(c_35552,plain,
    ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_35548,c_10])).

cnf(c_40380,plain,
    ( k4_xboole_0(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_40305,c_1079])).

cnf(c_42268,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_41499,c_35552,c_40380])).

cnf(c_42269,plain,
    ( k4_xboole_0(sK3,sK5) = sK4 ),
    inference(demodulation,[status(thm)],[c_42268,c_9])).

cnf(c_1064,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_11])).

cnf(c_48835,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,sK4),X0) ),
    inference(superposition,[status(thm)],[c_42269,c_1064])).

cnf(c_49040,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k4_xboole_0(sK3,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_48835,c_11])).

cnf(c_52545,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_52476,c_2,c_45759,c_49040])).

cnf(c_88796,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK5)) ),
    inference(superposition,[status(thm)],[c_628,c_49040])).

cnf(c_88997,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_88796,c_49040])).

cnf(c_36660,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_36635,c_0])).

cnf(c_1993,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK4,k2_xboole_0(X0,sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_518,c_1834])).

cnf(c_1768,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_245,c_518])).

cnf(c_2014,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1993,c_1768])).

cnf(c_12175,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_245,c_11227])).

cnf(c_35612,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) ),
    inference(superposition,[status(thm)],[c_35539,c_12175])).

cnf(c_33618,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_725,c_31374])).

cnf(c_12170,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_245,c_11227])).

cnf(c_34478,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK5,X1)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
    inference(superposition,[status(thm)],[c_34376,c_12170])).

cnf(c_31890,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X1) ),
    inference(superposition,[status(thm)],[c_31650,c_13])).

cnf(c_5234,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1867])).

cnf(c_8078,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_245,c_5234])).

cnf(c_2005,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1834,c_8])).

cnf(c_2008,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2005,c_6])).

cnf(c_5423,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_566,c_2008])).

cnf(c_5531,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5423,c_566,c_2801])).

cnf(c_8254,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8078,c_5531])).

cnf(c_31931,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK5,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_31890,c_2984,c_8254])).

cnf(c_34489,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_34478,c_31931,c_34373])).

cnf(c_34434,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
    inference(superposition,[status(thm)],[c_34376,c_1177])).

cnf(c_34549,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_34434,c_34376])).

cnf(c_35618,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_35612,c_1014,c_33618,c_34373,c_34489,c_34549])).

cnf(c_40578,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2014,c_2014,c_35618])).

cnf(c_40611,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_992,c_40578])).

cnf(c_33619,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_682,c_31374])).

cnf(c_40720,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_40611,c_33619])).

cnf(c_1008,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_244,c_10])).

cnf(c_45840,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_29994,c_1008])).

cnf(c_2774,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_989,c_1079])).

cnf(c_46013,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45840,c_11,c_2774])).

cnf(c_46289,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[status(thm)],[c_46013,c_11])).

cnf(c_1227,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_525,c_10])).

cnf(c_1244,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1227,c_238])).

cnf(c_46323,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46289,c_11,c_1244,c_8254])).

cnf(c_49883,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_46323])).

cnf(c_1106,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_12,c_8])).

cnf(c_11811,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_12,c_2104])).

cnf(c_11945,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2104,c_243])).

cnf(c_12094,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_11811,c_11945])).

cnf(c_31549,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_29994,c_516])).

cnf(c_31656,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_31549,c_29994])).

cnf(c_54208,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1106,c_1106,c_12094,c_31656])).

cnf(c_54326,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49883,c_54208])).

cnf(c_46265,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34484,c_46013])).

cnf(c_1074,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_50608,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_46265,c_1074])).

cnf(c_35723,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK5),X0) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_35552,c_11])).

cnf(c_35744,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_35723,c_11])).

cnf(c_41497,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_40573,c_2716])).

cnf(c_41491,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK2)) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_40573,c_12])).

cnf(c_41546,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_41491,c_40573])).

cnf(c_41547,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_41546,c_40380])).

cnf(c_41548,plain,
    ( sK2 = sK5 ),
    inference(demodulation,[status(thm)],[c_41547,c_9])).

cnf(c_42273,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_41497,c_35744,c_41548])).

cnf(c_45485,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_35744,c_35744,c_42273])).

cnf(c_45488,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(X0,sK5)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_0,c_45485])).

cnf(c_2702,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_2231])).

cnf(c_45616,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK4,X0)) = sK5 ),
    inference(superposition,[status(thm)],[c_45488,c_2702])).

cnf(c_51003,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50608,c_6,c_11,c_238,c_45616])).

cnf(c_46933,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_46265,c_1075])).

cnf(c_46935,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK5 ),
    inference(demodulation,[status(thm)],[c_46933,c_6,c_11])).

cnf(c_50664,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
    inference(superposition,[status(thm)],[c_46935,c_1074])).

cnf(c_47537,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(X1,sK5)) = k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_46935,c_2702])).

cnf(c_50948,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_50664,c_47537])).

cnf(c_50950,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_50948])).

cnf(c_51004,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_51003,c_50950])).

cnf(c_54404,plain,
    ( k2_xboole_0(sP0_iProver_split,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_54326,c_51004])).

cnf(c_54405,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54404,c_6])).

cnf(c_61973,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_40720,c_40720,c_54405])).

cnf(c_61976,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_61973])).

cnf(c_63997,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK5,sK3))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_31360,c_61976])).

cnf(c_31389,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_31360,c_1280])).

cnf(c_31399,plain,
    ( k2_xboole_0(sK5,sK3) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_31389,c_1177])).

cnf(c_4243,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK4,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3927,c_243])).

cnf(c_11969,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_2104,c_4243])).

cnf(c_11972,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_11969,c_3927])).

cnf(c_12589,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_11972,c_518])).

cnf(c_33631,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_12589,c_31374])).

cnf(c_13983,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK4),sK5),sK4) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_12589,c_989])).

cnf(c_3905,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1177,c_518])).

cnf(c_3926,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3905,c_153,c_1282])).

cnf(c_14034,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK4),sK5),sK4) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_13983,c_3926])).

cnf(c_4766,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_573,c_573,c_2231])).

cnf(c_15709,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5))) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_14034,c_4766])).

cnf(c_575,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_153,c_10])).

cnf(c_633,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_575,c_1])).

cnf(c_7473,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_633,c_633,c_1843])).

cnf(c_7474,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_7473,c_9,c_633])).

cnf(c_15744,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_15709,c_2716,c_7474])).

cnf(c_33754,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_33631,c_15744])).

cnf(c_64184,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_63997,c_31399,c_33754])).

cnf(c_88998,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK4,k1_xboole_0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_88997,c_9949,c_36660,c_64184])).

cnf(c_54504,plain,
    ( k2_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_54405,c_6])).

cnf(c_88999,plain,
    ( k4_xboole_0(sK3,sK4) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_88998,c_54405,c_54504])).

cnf(c_93628,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_52545,c_52545,c_88999])).

cnf(c_93696,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,sK3))) = k2_xboole_0(sK4,sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_93628,c_1075])).

cnf(c_51207,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),sK4),k2_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),sK4),k4_xboole_0(sK4,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_51003,c_628])).

cnf(c_2740,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_8,c_989])).

cnf(c_2830,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2740,c_989])).

cnf(c_51229,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),sK4) = k2_xboole_0(X0,sK3) ),
    inference(demodulation,[status(thm)],[c_51207,c_9,c_2830,c_31656])).

cnf(c_46295,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_46013,c_628])).

cnf(c_46316,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_46295,c_11,c_31656])).

cnf(c_46317,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_46316,c_6,c_2830])).

cnf(c_49570,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_46317,c_0])).

cnf(c_53805,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_49570])).

cnf(c_56896,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK4,k2_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_51229,c_53805])).

cnf(c_51328,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,X0),sK4) = k2_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_51229])).

cnf(c_56899,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK4,k2_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_51328,c_53805])).

cnf(c_53759,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_42269,c_49570])).

cnf(c_57003,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK3,X1) ),
    inference(demodulation,[status(thm)],[c_56899,c_53759])).

cnf(c_57007,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_56896,c_57003])).

cnf(c_29047,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_991,c_992])).

cnf(c_29132,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_29047,c_1014])).

cnf(c_34319,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_33616,c_1177])).

cnf(c_34321,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_33616,c_989])).

cnf(c_8095,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_869,c_5234])).

cnf(c_2918,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_869,c_990])).

cnf(c_2974,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_2918,c_2962])).

cnf(c_8240,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_8095,c_2974])).

cnf(c_34649,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_34321,c_8240])).

cnf(c_34651,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_34319,c_34649])).

cnf(c_34374,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_34373,c_33616])).

cnf(c_34652,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_34651,c_33619,c_34373,c_34374])).

cnf(c_82319,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_29132,c_29132,c_34652])).

cnf(c_1189,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_13,c_10])).

cnf(c_82374,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK5,sK4),k4_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_82319,c_1189])).

cnf(c_82469,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_82374,c_36635])).

cnf(c_12942,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_2716,c_4766])).

cnf(c_12953,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_12942,c_8254])).

cnf(c_12954,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_12953,c_8])).

cnf(c_82470,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK5,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_82469,c_12954])).

cnf(c_93700,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK5,sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_93696,c_54504,c_57007,c_82470])).

cnf(c_7147,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_2702])).

cnf(c_13399,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = sK5 ),
    inference(superposition,[status(thm)],[c_1768,c_7147])).

cnf(c_54810,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK5,X1)))) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_13399,c_13399,c_41548])).

cnf(c_54868,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k4_xboole_0(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_54810,c_12])).

cnf(c_3034,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1766,c_1834])).

cnf(c_42525,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3034,c_3034,c_35618])).

cnf(c_54489,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_54405,c_42525])).

cnf(c_54894,plain,
    ( k4_xboole_0(sK5,sK5) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_54868,c_54489])).

cnf(c_93701,plain,
    ( k2_xboole_0(sK3,sP0_iProver_split) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_93700,c_54894])).

cnf(c_93702,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_93701,c_54504])).

cnf(c_155,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1130,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_156,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_249,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_463,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_14,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93702,c_1130,c_463,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 28.00/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.00/4.00  
% 28.00/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 28.00/4.00  
% 28.00/4.00  ------  iProver source info
% 28.00/4.00  
% 28.00/4.00  git: date: 2020-06-30 10:37:57 +0100
% 28.00/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 28.00/4.00  git: non_committed_changes: false
% 28.00/4.00  git: last_make_outside_of_git: false
% 28.00/4.00  
% 28.00/4.00  ------ 
% 28.00/4.00  
% 28.00/4.00  ------ Input Options
% 28.00/4.00  
% 28.00/4.00  --out_options                           all
% 28.00/4.00  --tptp_safe_out                         true
% 28.00/4.00  --problem_path                          ""
% 28.00/4.00  --include_path                          ""
% 28.00/4.00  --clausifier                            res/vclausify_rel
% 28.00/4.00  --clausifier_options                    ""
% 28.00/4.00  --stdin                                 false
% 28.00/4.00  --stats_out                             all
% 28.00/4.00  
% 28.00/4.00  ------ General Options
% 28.00/4.00  
% 28.00/4.00  --fof                                   false
% 28.00/4.00  --time_out_real                         305.
% 28.00/4.00  --time_out_virtual                      -1.
% 28.00/4.00  --symbol_type_check                     false
% 28.00/4.00  --clausify_out                          false
% 28.00/4.00  --sig_cnt_out                           false
% 28.00/4.00  --trig_cnt_out                          false
% 28.00/4.00  --trig_cnt_out_tolerance                1.
% 28.00/4.00  --trig_cnt_out_sk_spl                   false
% 28.00/4.00  --abstr_cl_out                          false
% 28.00/4.00  
% 28.00/4.00  ------ Global Options
% 28.00/4.00  
% 28.00/4.00  --schedule                              default
% 28.00/4.00  --add_important_lit                     false
% 28.00/4.00  --prop_solver_per_cl                    1000
% 28.00/4.00  --min_unsat_core                        false
% 28.00/4.00  --soft_assumptions                      false
% 28.00/4.00  --soft_lemma_size                       3
% 28.00/4.00  --prop_impl_unit_size                   0
% 28.00/4.00  --prop_impl_unit                        []
% 28.00/4.00  --share_sel_clauses                     true
% 28.00/4.00  --reset_solvers                         false
% 28.00/4.00  --bc_imp_inh                            [conj_cone]
% 28.00/4.00  --conj_cone_tolerance                   3.
% 28.00/4.00  --extra_neg_conj                        none
% 28.00/4.00  --large_theory_mode                     true
% 28.00/4.00  --prolific_symb_bound                   200
% 28.00/4.00  --lt_threshold                          2000
% 28.00/4.00  --clause_weak_htbl                      true
% 28.00/4.00  --gc_record_bc_elim                     false
% 28.00/4.00  
% 28.00/4.00  ------ Preprocessing Options
% 28.00/4.00  
% 28.00/4.00  --preprocessing_flag                    true
% 28.00/4.00  --time_out_prep_mult                    0.1
% 28.00/4.00  --splitting_mode                        input
% 28.00/4.00  --splitting_grd                         true
% 28.00/4.00  --splitting_cvd                         false
% 28.00/4.00  --splitting_cvd_svl                     false
% 28.00/4.00  --splitting_nvd                         32
% 28.00/4.00  --sub_typing                            true
% 28.00/4.00  --prep_gs_sim                           true
% 28.00/4.00  --prep_unflatten                        true
% 28.00/4.00  --prep_res_sim                          true
% 28.00/4.00  --prep_upred                            true
% 28.00/4.00  --prep_sem_filter                       exhaustive
% 28.00/4.00  --prep_sem_filter_out                   false
% 28.00/4.00  --pred_elim                             true
% 28.00/4.00  --res_sim_input                         true
% 28.00/4.00  --eq_ax_congr_red                       true
% 28.00/4.00  --pure_diseq_elim                       true
% 28.00/4.00  --brand_transform                       false
% 28.00/4.00  --non_eq_to_eq                          false
% 28.00/4.00  --prep_def_merge                        true
% 28.00/4.00  --prep_def_merge_prop_impl              false
% 28.00/4.00  --prep_def_merge_mbd                    true
% 28.00/4.00  --prep_def_merge_tr_red                 false
% 28.00/4.00  --prep_def_merge_tr_cl                  false
% 28.00/4.00  --smt_preprocessing                     true
% 28.00/4.00  --smt_ac_axioms                         fast
% 28.00/4.00  --preprocessed_out                      false
% 28.00/4.00  --preprocessed_stats                    false
% 28.00/4.00  
% 28.00/4.00  ------ Abstraction refinement Options
% 28.00/4.00  
% 28.00/4.00  --abstr_ref                             []
% 28.00/4.00  --abstr_ref_prep                        false
% 28.00/4.00  --abstr_ref_until_sat                   false
% 28.00/4.00  --abstr_ref_sig_restrict                funpre
% 28.00/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 28.00/4.00  --abstr_ref_under                       []
% 28.00/4.00  
% 28.00/4.00  ------ SAT Options
% 28.00/4.00  
% 28.00/4.00  --sat_mode                              false
% 28.00/4.00  --sat_fm_restart_options                ""
% 28.00/4.00  --sat_gr_def                            false
% 28.00/4.00  --sat_epr_types                         true
% 28.00/4.00  --sat_non_cyclic_types                  false
% 28.00/4.00  --sat_finite_models                     false
% 28.00/4.00  --sat_fm_lemmas                         false
% 28.00/4.00  --sat_fm_prep                           false
% 28.00/4.00  --sat_fm_uc_incr                        true
% 28.00/4.00  --sat_out_model                         small
% 28.00/4.00  --sat_out_clauses                       false
% 28.00/4.00  
% 28.00/4.00  ------ QBF Options
% 28.00/4.00  
% 28.00/4.00  --qbf_mode                              false
% 28.00/4.00  --qbf_elim_univ                         false
% 28.00/4.00  --qbf_dom_inst                          none
% 28.00/4.00  --qbf_dom_pre_inst                      false
% 28.00/4.00  --qbf_sk_in                             false
% 28.00/4.00  --qbf_pred_elim                         true
% 28.00/4.00  --qbf_split                             512
% 28.00/4.00  
% 28.00/4.00  ------ BMC1 Options
% 28.00/4.00  
% 28.00/4.00  --bmc1_incremental                      false
% 28.00/4.00  --bmc1_axioms                           reachable_all
% 28.00/4.00  --bmc1_min_bound                        0
% 28.00/4.00  --bmc1_max_bound                        -1
% 28.00/4.00  --bmc1_max_bound_default                -1
% 28.00/4.00  --bmc1_symbol_reachability              true
% 28.00/4.00  --bmc1_property_lemmas                  false
% 28.00/4.00  --bmc1_k_induction                      false
% 28.00/4.00  --bmc1_non_equiv_states                 false
% 28.00/4.00  --bmc1_deadlock                         false
% 28.00/4.00  --bmc1_ucm                              false
% 28.00/4.00  --bmc1_add_unsat_core                   none
% 28.00/4.00  --bmc1_unsat_core_children              false
% 28.00/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 28.00/4.00  --bmc1_out_stat                         full
% 28.00/4.00  --bmc1_ground_init                      false
% 28.00/4.00  --bmc1_pre_inst_next_state              false
% 28.00/4.00  --bmc1_pre_inst_state                   false
% 28.00/4.00  --bmc1_pre_inst_reach_state             false
% 28.00/4.00  --bmc1_out_unsat_core                   false
% 28.00/4.00  --bmc1_aig_witness_out                  false
% 28.00/4.00  --bmc1_verbose                          false
% 28.00/4.00  --bmc1_dump_clauses_tptp                false
% 28.00/4.00  --bmc1_dump_unsat_core_tptp             false
% 28.00/4.00  --bmc1_dump_file                        -
% 28.00/4.00  --bmc1_ucm_expand_uc_limit              128
% 28.00/4.00  --bmc1_ucm_n_expand_iterations          6
% 28.00/4.00  --bmc1_ucm_extend_mode                  1
% 28.00/4.00  --bmc1_ucm_init_mode                    2
% 28.00/4.00  --bmc1_ucm_cone_mode                    none
% 28.00/4.00  --bmc1_ucm_reduced_relation_type        0
% 28.00/4.00  --bmc1_ucm_relax_model                  4
% 28.00/4.00  --bmc1_ucm_full_tr_after_sat            true
% 28.00/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 28.00/4.00  --bmc1_ucm_layered_model                none
% 28.00/4.00  --bmc1_ucm_max_lemma_size               10
% 28.00/4.00  
% 28.00/4.00  ------ AIG Options
% 28.00/4.00  
% 28.00/4.00  --aig_mode                              false
% 28.00/4.00  
% 28.00/4.00  ------ Instantiation Options
% 28.00/4.00  
% 28.00/4.00  --instantiation_flag                    true
% 28.00/4.00  --inst_sos_flag                         true
% 28.00/4.00  --inst_sos_phase                        true
% 28.00/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.00/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.00/4.00  --inst_lit_sel_side                     num_symb
% 28.00/4.00  --inst_solver_per_active                1400
% 28.00/4.00  --inst_solver_calls_frac                1.
% 28.00/4.00  --inst_passive_queue_type               priority_queues
% 28.00/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.00/4.00  --inst_passive_queues_freq              [25;2]
% 28.00/4.00  --inst_dismatching                      true
% 28.00/4.00  --inst_eager_unprocessed_to_passive     true
% 28.00/4.00  --inst_prop_sim_given                   true
% 28.00/4.00  --inst_prop_sim_new                     false
% 28.00/4.00  --inst_subs_new                         false
% 28.00/4.00  --inst_eq_res_simp                      false
% 28.00/4.00  --inst_subs_given                       false
% 28.00/4.00  --inst_orphan_elimination               true
% 28.00/4.00  --inst_learning_loop_flag               true
% 28.00/4.00  --inst_learning_start                   3000
% 28.00/4.00  --inst_learning_factor                  2
% 28.00/4.00  --inst_start_prop_sim_after_learn       3
% 28.00/4.00  --inst_sel_renew                        solver
% 28.00/4.00  --inst_lit_activity_flag                true
% 28.00/4.00  --inst_restr_to_given                   false
% 28.00/4.00  --inst_activity_threshold               500
% 28.00/4.00  --inst_out_proof                        true
% 28.00/4.00  
% 28.00/4.00  ------ Resolution Options
% 28.00/4.00  
% 28.00/4.00  --resolution_flag                       true
% 28.00/4.00  --res_lit_sel                           adaptive
% 28.00/4.00  --res_lit_sel_side                      none
% 28.00/4.00  --res_ordering                          kbo
% 28.00/4.00  --res_to_prop_solver                    active
% 28.00/4.00  --res_prop_simpl_new                    false
% 28.00/4.00  --res_prop_simpl_given                  true
% 28.00/4.00  --res_passive_queue_type                priority_queues
% 28.00/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.00/4.00  --res_passive_queues_freq               [15;5]
% 28.00/4.00  --res_forward_subs                      full
% 28.00/4.00  --res_backward_subs                     full
% 28.00/4.00  --res_forward_subs_resolution           true
% 28.00/4.00  --res_backward_subs_resolution          true
% 28.00/4.00  --res_orphan_elimination                true
% 28.00/4.00  --res_time_limit                        2.
% 28.00/4.00  --res_out_proof                         true
% 28.00/4.00  
% 28.00/4.00  ------ Superposition Options
% 28.00/4.00  
% 28.00/4.00  --superposition_flag                    true
% 28.00/4.00  --sup_passive_queue_type                priority_queues
% 28.00/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.00/4.00  --sup_passive_queues_freq               [8;1;4]
% 28.00/4.00  --demod_completeness_check              fast
% 28.00/4.00  --demod_use_ground                      true
% 28.00/4.00  --sup_to_prop_solver                    passive
% 28.00/4.00  --sup_prop_simpl_new                    true
% 28.00/4.00  --sup_prop_simpl_given                  true
% 28.00/4.00  --sup_fun_splitting                     true
% 28.00/4.00  --sup_smt_interval                      50000
% 28.00/4.00  
% 28.00/4.00  ------ Superposition Simplification Setup
% 28.00/4.00  
% 28.00/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 28.00/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 28.00/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 28.00/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 28.00/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 28.00/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 28.00/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 28.00/4.00  --sup_immed_triv                        [TrivRules]
% 28.00/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_immed_bw_main                     []
% 28.00/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 28.00/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 28.00/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_input_bw                          []
% 28.00/4.00  
% 28.00/4.00  ------ Combination Options
% 28.00/4.00  
% 28.00/4.00  --comb_res_mult                         3
% 28.00/4.00  --comb_sup_mult                         2
% 28.00/4.00  --comb_inst_mult                        10
% 28.00/4.00  
% 28.00/4.00  ------ Debug Options
% 28.00/4.00  
% 28.00/4.00  --dbg_backtrace                         false
% 28.00/4.00  --dbg_dump_prop_clauses                 false
% 28.00/4.00  --dbg_dump_prop_clauses_file            -
% 28.00/4.00  --dbg_out_stat                          false
% 28.00/4.00  ------ Parsing...
% 28.00/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 28.00/4.00  
% 28.00/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 28.00/4.00  
% 28.00/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 28.00/4.00  
% 28.00/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 28.00/4.00  ------ Proving...
% 28.00/4.00  ------ Problem Properties 
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  clauses                                 17
% 28.00/4.00  conjectures                             2
% 28.00/4.00  EPR                                     1
% 28.00/4.00  Horn                                    16
% 28.00/4.00  unary                                   15
% 28.00/4.00  binary                                  2
% 28.00/4.00  lits                                    19
% 28.00/4.00  lits eq                                 14
% 28.00/4.00  fd_pure                                 0
% 28.00/4.00  fd_pseudo                               0
% 28.00/4.00  fd_cond                                 1
% 28.00/4.00  fd_pseudo_cond                          0
% 28.00/4.00  AC symbols                              1
% 28.00/4.00  
% 28.00/4.00  ------ Schedule dynamic 5 is on 
% 28.00/4.00  
% 28.00/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  ------ 
% 28.00/4.00  Current options:
% 28.00/4.00  ------ 
% 28.00/4.00  
% 28.00/4.00  ------ Input Options
% 28.00/4.00  
% 28.00/4.00  --out_options                           all
% 28.00/4.00  --tptp_safe_out                         true
% 28.00/4.00  --problem_path                          ""
% 28.00/4.00  --include_path                          ""
% 28.00/4.00  --clausifier                            res/vclausify_rel
% 28.00/4.00  --clausifier_options                    ""
% 28.00/4.00  --stdin                                 false
% 28.00/4.00  --stats_out                             all
% 28.00/4.00  
% 28.00/4.00  ------ General Options
% 28.00/4.00  
% 28.00/4.00  --fof                                   false
% 28.00/4.00  --time_out_real                         305.
% 28.00/4.00  --time_out_virtual                      -1.
% 28.00/4.00  --symbol_type_check                     false
% 28.00/4.00  --clausify_out                          false
% 28.00/4.00  --sig_cnt_out                           false
% 28.00/4.00  --trig_cnt_out                          false
% 28.00/4.00  --trig_cnt_out_tolerance                1.
% 28.00/4.00  --trig_cnt_out_sk_spl                   false
% 28.00/4.00  --abstr_cl_out                          false
% 28.00/4.00  
% 28.00/4.00  ------ Global Options
% 28.00/4.00  
% 28.00/4.00  --schedule                              default
% 28.00/4.00  --add_important_lit                     false
% 28.00/4.00  --prop_solver_per_cl                    1000
% 28.00/4.00  --min_unsat_core                        false
% 28.00/4.00  --soft_assumptions                      false
% 28.00/4.00  --soft_lemma_size                       3
% 28.00/4.00  --prop_impl_unit_size                   0
% 28.00/4.00  --prop_impl_unit                        []
% 28.00/4.00  --share_sel_clauses                     true
% 28.00/4.00  --reset_solvers                         false
% 28.00/4.00  --bc_imp_inh                            [conj_cone]
% 28.00/4.00  --conj_cone_tolerance                   3.
% 28.00/4.00  --extra_neg_conj                        none
% 28.00/4.00  --large_theory_mode                     true
% 28.00/4.00  --prolific_symb_bound                   200
% 28.00/4.00  --lt_threshold                          2000
% 28.00/4.00  --clause_weak_htbl                      true
% 28.00/4.00  --gc_record_bc_elim                     false
% 28.00/4.00  
% 28.00/4.00  ------ Preprocessing Options
% 28.00/4.00  
% 28.00/4.00  --preprocessing_flag                    true
% 28.00/4.00  --time_out_prep_mult                    0.1
% 28.00/4.00  --splitting_mode                        input
% 28.00/4.00  --splitting_grd                         true
% 28.00/4.00  --splitting_cvd                         false
% 28.00/4.00  --splitting_cvd_svl                     false
% 28.00/4.00  --splitting_nvd                         32
% 28.00/4.00  --sub_typing                            true
% 28.00/4.00  --prep_gs_sim                           true
% 28.00/4.00  --prep_unflatten                        true
% 28.00/4.00  --prep_res_sim                          true
% 28.00/4.00  --prep_upred                            true
% 28.00/4.00  --prep_sem_filter                       exhaustive
% 28.00/4.00  --prep_sem_filter_out                   false
% 28.00/4.00  --pred_elim                             true
% 28.00/4.00  --res_sim_input                         true
% 28.00/4.00  --eq_ax_congr_red                       true
% 28.00/4.00  --pure_diseq_elim                       true
% 28.00/4.00  --brand_transform                       false
% 28.00/4.00  --non_eq_to_eq                          false
% 28.00/4.00  --prep_def_merge                        true
% 28.00/4.00  --prep_def_merge_prop_impl              false
% 28.00/4.00  --prep_def_merge_mbd                    true
% 28.00/4.00  --prep_def_merge_tr_red                 false
% 28.00/4.00  --prep_def_merge_tr_cl                  false
% 28.00/4.00  --smt_preprocessing                     true
% 28.00/4.00  --smt_ac_axioms                         fast
% 28.00/4.00  --preprocessed_out                      false
% 28.00/4.00  --preprocessed_stats                    false
% 28.00/4.00  
% 28.00/4.00  ------ Abstraction refinement Options
% 28.00/4.00  
% 28.00/4.00  --abstr_ref                             []
% 28.00/4.00  --abstr_ref_prep                        false
% 28.00/4.00  --abstr_ref_until_sat                   false
% 28.00/4.00  --abstr_ref_sig_restrict                funpre
% 28.00/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 28.00/4.00  --abstr_ref_under                       []
% 28.00/4.00  
% 28.00/4.00  ------ SAT Options
% 28.00/4.00  
% 28.00/4.00  --sat_mode                              false
% 28.00/4.00  --sat_fm_restart_options                ""
% 28.00/4.00  --sat_gr_def                            false
% 28.00/4.00  --sat_epr_types                         true
% 28.00/4.00  --sat_non_cyclic_types                  false
% 28.00/4.00  --sat_finite_models                     false
% 28.00/4.00  --sat_fm_lemmas                         false
% 28.00/4.00  --sat_fm_prep                           false
% 28.00/4.00  --sat_fm_uc_incr                        true
% 28.00/4.00  --sat_out_model                         small
% 28.00/4.00  --sat_out_clauses                       false
% 28.00/4.00  
% 28.00/4.00  ------ QBF Options
% 28.00/4.00  
% 28.00/4.00  --qbf_mode                              false
% 28.00/4.00  --qbf_elim_univ                         false
% 28.00/4.00  --qbf_dom_inst                          none
% 28.00/4.00  --qbf_dom_pre_inst                      false
% 28.00/4.00  --qbf_sk_in                             false
% 28.00/4.00  --qbf_pred_elim                         true
% 28.00/4.00  --qbf_split                             512
% 28.00/4.00  
% 28.00/4.00  ------ BMC1 Options
% 28.00/4.00  
% 28.00/4.00  --bmc1_incremental                      false
% 28.00/4.00  --bmc1_axioms                           reachable_all
% 28.00/4.00  --bmc1_min_bound                        0
% 28.00/4.00  --bmc1_max_bound                        -1
% 28.00/4.00  --bmc1_max_bound_default                -1
% 28.00/4.00  --bmc1_symbol_reachability              true
% 28.00/4.00  --bmc1_property_lemmas                  false
% 28.00/4.00  --bmc1_k_induction                      false
% 28.00/4.00  --bmc1_non_equiv_states                 false
% 28.00/4.00  --bmc1_deadlock                         false
% 28.00/4.00  --bmc1_ucm                              false
% 28.00/4.00  --bmc1_add_unsat_core                   none
% 28.00/4.00  --bmc1_unsat_core_children              false
% 28.00/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 28.00/4.00  --bmc1_out_stat                         full
% 28.00/4.00  --bmc1_ground_init                      false
% 28.00/4.00  --bmc1_pre_inst_next_state              false
% 28.00/4.00  --bmc1_pre_inst_state                   false
% 28.00/4.00  --bmc1_pre_inst_reach_state             false
% 28.00/4.00  --bmc1_out_unsat_core                   false
% 28.00/4.00  --bmc1_aig_witness_out                  false
% 28.00/4.00  --bmc1_verbose                          false
% 28.00/4.00  --bmc1_dump_clauses_tptp                false
% 28.00/4.00  --bmc1_dump_unsat_core_tptp             false
% 28.00/4.00  --bmc1_dump_file                        -
% 28.00/4.00  --bmc1_ucm_expand_uc_limit              128
% 28.00/4.00  --bmc1_ucm_n_expand_iterations          6
% 28.00/4.00  --bmc1_ucm_extend_mode                  1
% 28.00/4.00  --bmc1_ucm_init_mode                    2
% 28.00/4.00  --bmc1_ucm_cone_mode                    none
% 28.00/4.00  --bmc1_ucm_reduced_relation_type        0
% 28.00/4.00  --bmc1_ucm_relax_model                  4
% 28.00/4.00  --bmc1_ucm_full_tr_after_sat            true
% 28.00/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 28.00/4.00  --bmc1_ucm_layered_model                none
% 28.00/4.00  --bmc1_ucm_max_lemma_size               10
% 28.00/4.00  
% 28.00/4.00  ------ AIG Options
% 28.00/4.00  
% 28.00/4.00  --aig_mode                              false
% 28.00/4.00  
% 28.00/4.00  ------ Instantiation Options
% 28.00/4.00  
% 28.00/4.00  --instantiation_flag                    true
% 28.00/4.00  --inst_sos_flag                         true
% 28.00/4.00  --inst_sos_phase                        true
% 28.00/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.00/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.00/4.00  --inst_lit_sel_side                     none
% 28.00/4.00  --inst_solver_per_active                1400
% 28.00/4.00  --inst_solver_calls_frac                1.
% 28.00/4.00  --inst_passive_queue_type               priority_queues
% 28.00/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.00/4.00  --inst_passive_queues_freq              [25;2]
% 28.00/4.00  --inst_dismatching                      true
% 28.00/4.00  --inst_eager_unprocessed_to_passive     true
% 28.00/4.00  --inst_prop_sim_given                   true
% 28.00/4.00  --inst_prop_sim_new                     false
% 28.00/4.00  --inst_subs_new                         false
% 28.00/4.00  --inst_eq_res_simp                      false
% 28.00/4.00  --inst_subs_given                       false
% 28.00/4.00  --inst_orphan_elimination               true
% 28.00/4.00  --inst_learning_loop_flag               true
% 28.00/4.00  --inst_learning_start                   3000
% 28.00/4.00  --inst_learning_factor                  2
% 28.00/4.00  --inst_start_prop_sim_after_learn       3
% 28.00/4.00  --inst_sel_renew                        solver
% 28.00/4.00  --inst_lit_activity_flag                true
% 28.00/4.00  --inst_restr_to_given                   false
% 28.00/4.00  --inst_activity_threshold               500
% 28.00/4.00  --inst_out_proof                        true
% 28.00/4.00  
% 28.00/4.00  ------ Resolution Options
% 28.00/4.00  
% 28.00/4.00  --resolution_flag                       false
% 28.00/4.00  --res_lit_sel                           adaptive
% 28.00/4.00  --res_lit_sel_side                      none
% 28.00/4.00  --res_ordering                          kbo
% 28.00/4.00  --res_to_prop_solver                    active
% 28.00/4.00  --res_prop_simpl_new                    false
% 28.00/4.00  --res_prop_simpl_given                  true
% 28.00/4.00  --res_passive_queue_type                priority_queues
% 28.00/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.00/4.00  --res_passive_queues_freq               [15;5]
% 28.00/4.00  --res_forward_subs                      full
% 28.00/4.00  --res_backward_subs                     full
% 28.00/4.00  --res_forward_subs_resolution           true
% 28.00/4.00  --res_backward_subs_resolution          true
% 28.00/4.00  --res_orphan_elimination                true
% 28.00/4.00  --res_time_limit                        2.
% 28.00/4.00  --res_out_proof                         true
% 28.00/4.00  
% 28.00/4.00  ------ Superposition Options
% 28.00/4.00  
% 28.00/4.00  --superposition_flag                    true
% 28.00/4.00  --sup_passive_queue_type                priority_queues
% 28.00/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.00/4.00  --sup_passive_queues_freq               [8;1;4]
% 28.00/4.00  --demod_completeness_check              fast
% 28.00/4.00  --demod_use_ground                      true
% 28.00/4.00  --sup_to_prop_solver                    passive
% 28.00/4.00  --sup_prop_simpl_new                    true
% 28.00/4.00  --sup_prop_simpl_given                  true
% 28.00/4.00  --sup_fun_splitting                     true
% 28.00/4.00  --sup_smt_interval                      50000
% 28.00/4.00  
% 28.00/4.00  ------ Superposition Simplification Setup
% 28.00/4.00  
% 28.00/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 28.00/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 28.00/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 28.00/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 28.00/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 28.00/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 28.00/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 28.00/4.00  --sup_immed_triv                        [TrivRules]
% 28.00/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_immed_bw_main                     []
% 28.00/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 28.00/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 28.00/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 28.00/4.00  --sup_input_bw                          []
% 28.00/4.00  
% 28.00/4.00  ------ Combination Options
% 28.00/4.00  
% 28.00/4.00  --comb_res_mult                         3
% 28.00/4.00  --comb_sup_mult                         2
% 28.00/4.00  --comb_inst_mult                        10
% 28.00/4.00  
% 28.00/4.00  ------ Debug Options
% 28.00/4.00  
% 28.00/4.00  --dbg_backtrace                         false
% 28.00/4.00  --dbg_dump_prop_clauses                 false
% 28.00/4.00  --dbg_dump_prop_clauses_file            -
% 28.00/4.00  --dbg_out_stat                          false
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  ------ Proving...
% 28.00/4.00  
% 28.00/4.00  
% 28.00/4.00  % SZS status Theorem for theBenchmark.p
% 28.00/4.00  
% 28.00/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 28.00/4.00  
% 28.00/4.00  fof(f8,axiom,(
% 28.00/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f37,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 28.00/4.00    inference(cnf_transformation,[],[f8])).
% 28.00/4.00  
% 28.00/4.00  fof(f3,axiom,(
% 28.00/4.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f17,plain,(
% 28.00/4.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 28.00/4.00    inference(rectify,[],[f3])).
% 28.00/4.00  
% 28.00/4.00  fof(f31,plain,(
% 28.00/4.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 28.00/4.00    inference(cnf_transformation,[],[f17])).
% 28.00/4.00  
% 28.00/4.00  fof(f14,axiom,(
% 28.00/4.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f43,plain,(
% 28.00/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 28.00/4.00    inference(cnf_transformation,[],[f14])).
% 28.00/4.00  
% 28.00/4.00  fof(f1,axiom,(
% 28.00/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f29,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 28.00/4.00    inference(cnf_transformation,[],[f1])).
% 28.00/4.00  
% 28.00/4.00  fof(f15,conjecture,(
% 28.00/4.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f16,negated_conjecture,(
% 28.00/4.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 28.00/4.00    inference(negated_conjecture,[],[f15])).
% 28.00/4.00  
% 28.00/4.00  fof(f21,plain,(
% 28.00/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 28.00/4.00    inference(ennf_transformation,[],[f16])).
% 28.00/4.00  
% 28.00/4.00  fof(f22,plain,(
% 28.00/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 28.00/4.00    inference(flattening,[],[f21])).
% 28.00/4.00  
% 28.00/4.00  fof(f27,plain,(
% 28.00/4.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5))),
% 28.00/4.00    introduced(choice_axiom,[])).
% 28.00/4.00  
% 28.00/4.00  fof(f28,plain,(
% 28.00/4.00    sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 28.00/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f27])).
% 28.00/4.00  
% 28.00/4.00  fof(f44,plain,(
% 28.00/4.00    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 28.00/4.00    inference(cnf_transformation,[],[f28])).
% 28.00/4.00  
% 28.00/4.00  fof(f6,axiom,(
% 28.00/4.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f35,plain,(
% 28.00/4.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.00/4.00    inference(cnf_transformation,[],[f6])).
% 28.00/4.00  
% 28.00/4.00  fof(f11,axiom,(
% 28.00/4.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f40,plain,(
% 28.00/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 28.00/4.00    inference(cnf_transformation,[],[f11])).
% 28.00/4.00  
% 28.00/4.00  fof(f7,axiom,(
% 28.00/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f36,plain,(
% 28.00/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 28.00/4.00    inference(cnf_transformation,[],[f7])).
% 28.00/4.00  
% 28.00/4.00  fof(f13,axiom,(
% 28.00/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f42,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 28.00/4.00    inference(cnf_transformation,[],[f13])).
% 28.00/4.00  
% 28.00/4.00  fof(f51,plain,(
% 28.00/4.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 28.00/4.00    inference(definition_unfolding,[],[f36,f42])).
% 28.00/4.00  
% 28.00/4.00  fof(f9,axiom,(
% 28.00/4.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f38,plain,(
% 28.00/4.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 28.00/4.00    inference(cnf_transformation,[],[f9])).
% 28.00/4.00  
% 28.00/4.00  fof(f10,axiom,(
% 28.00/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f39,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 28.00/4.00    inference(cnf_transformation,[],[f10])).
% 28.00/4.00  
% 28.00/4.00  fof(f2,axiom,(
% 28.00/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f30,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 28.00/4.00    inference(cnf_transformation,[],[f2])).
% 28.00/4.00  
% 28.00/4.00  fof(f48,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 28.00/4.00    inference(definition_unfolding,[],[f30,f42,f42])).
% 28.00/4.00  
% 28.00/4.00  fof(f12,axiom,(
% 28.00/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f41,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 28.00/4.00    inference(cnf_transformation,[],[f12])).
% 28.00/4.00  
% 28.00/4.00  fof(f52,plain,(
% 28.00/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.00/4.00    inference(definition_unfolding,[],[f41,f42])).
% 28.00/4.00  
% 28.00/4.00  fof(f5,axiom,(
% 28.00/4.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f20,plain,(
% 28.00/4.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 28.00/4.00    inference(ennf_transformation,[],[f5])).
% 28.00/4.00  
% 28.00/4.00  fof(f25,plain,(
% 28.00/4.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 28.00/4.00    introduced(choice_axiom,[])).
% 28.00/4.00  
% 28.00/4.00  fof(f26,plain,(
% 28.00/4.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 28.00/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).
% 28.00/4.00  
% 28.00/4.00  fof(f34,plain,(
% 28.00/4.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 28.00/4.00    inference(cnf_transformation,[],[f26])).
% 28.00/4.00  
% 28.00/4.00  fof(f4,axiom,(
% 28.00/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 28.00/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.00/4.00  
% 28.00/4.00  fof(f18,plain,(
% 28.00/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 28.00/4.00    inference(rectify,[],[f4])).
% 28.00/4.00  
% 28.00/4.00  fof(f19,plain,(
% 28.00/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 28.00/4.00    inference(ennf_transformation,[],[f18])).
% 28.00/4.00  
% 28.00/4.00  fof(f23,plain,(
% 28.00/4.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 28.00/4.00    introduced(choice_axiom,[])).
% 28.00/4.00  
% 28.00/4.00  fof(f24,plain,(
% 28.00/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 28.00/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).
% 28.00/4.00  
% 28.00/4.00  fof(f33,plain,(
% 28.00/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 28.00/4.00    inference(cnf_transformation,[],[f24])).
% 28.00/4.00  
% 28.00/4.00  fof(f49,plain,(
% 28.00/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.00/4.00    inference(definition_unfolding,[],[f33,f42])).
% 28.00/4.00  
% 28.00/4.00  fof(f45,plain,(
% 28.00/4.00    r1_xboole_0(sK4,sK2)),
% 28.00/4.00    inference(cnf_transformation,[],[f28])).
% 28.00/4.00  
% 28.00/4.00  fof(f46,plain,(
% 28.00/4.00    r1_xboole_0(sK5,sK3)),
% 28.00/4.00    inference(cnf_transformation,[],[f28])).
% 28.00/4.00  
% 28.00/4.00  fof(f47,plain,(
% 28.00/4.00    sK3 != sK4),
% 28.00/4.00    inference(cnf_transformation,[],[f28])).
% 28.00/4.00  
% 28.00/4.00  cnf(c_8,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 28.00/4.00      inference(cnf_transformation,[],[f37]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2,plain,
% 28.00/4.00      ( k2_xboole_0(X0,X0) = X0 ),
% 28.00/4.00      inference(cnf_transformation,[],[f31]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_13,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 28.00/4.00      inference(cnf_transformation,[],[f43]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_0,plain,
% 28.00/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 28.00/4.00      inference(cnf_transformation,[],[f29]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_243,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_516,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2036,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_516]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_244,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_991,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2104,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2036,c_8,c_991]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_17,negated_conjecture,
% 28.00/4.00      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.00      inference(cnf_transformation,[],[f44]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_153,negated_conjecture,
% 28.00/4.00      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.00      inference(theory_normalisation,[status(thm)],[c_17,c_13,c_0]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_992,plain,
% 28.00/4.00      ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_153,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1280,plain,
% 28.00/4.00      ( k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_0,c_992]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_11960,plain,
% 28.00/4.00      ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK3),sK4)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2104,c_1280]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_6,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 28.00/4.00      inference(cnf_transformation,[],[f35]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_990,plain,
% 28.00/4.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_6,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_11,plain,
% 28.00/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 28.00/4.00      inference(cnf_transformation,[],[f40]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_7,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 28.00/4.00      inference(cnf_transformation,[],[f51]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 28.00/4.00      inference(cnf_transformation,[],[f38]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_238,plain,
% 28.00/4.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1078,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_11,c_238]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1079,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_1078,c_8]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1856,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_992,c_1079]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3361,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK4,k1_xboole_0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_990,c_1856]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3375,plain,
% 28.00/4.00      ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_3361,c_6]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1075,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29572,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k4_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_3375,c_1075]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29985,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k4_xboole_0(sK4,sK2)) = sK3 ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_29572,c_6]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1177,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2,c_13]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_518,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_153,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_691,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_518,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3904,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1177,c_691]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1282,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2,c_992]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1344,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK5,sK4) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1282,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3927,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_3904,c_153,c_1344]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_10,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 28.00/4.00      inference(cnf_transformation,[],[f39]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_4237,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_3927,c_10]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29570,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(sK4,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_4237,c_1075]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29988,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_29570,c_1075]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_571,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2208,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_153,c_571]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29989,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_29988,c_2208]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_566,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30212,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k2_xboole_0(sK4,sK5)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_29989,c_566]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30236,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_30212,c_153]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1012,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_244,c_518]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1014,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_1012,c_691]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30237,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30236,c_2,c_566,c_1014]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30405,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_30237,c_571]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30488,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_30405,c_2208]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 28.00/4.00      inference(cnf_transformation,[],[f48]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_12,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 28.00/4.00      inference(cnf_transformation,[],[f52]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1095,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1,c_12]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30532,plain,
% 28.00/4.00      ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_30488,c_1095]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30196,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_29989,c_10]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_628,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30521,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_30488,c_628]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30554,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30521,c_30488]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30199,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_29989,c_516]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30202,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_29989,c_991]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30239,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k2_xboole_0(sK2,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,X0)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30202,c_991]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30240,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30199,c_29989,c_30239]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30555,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4))))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_30554,c_30240]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2226,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_571,c_1]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_573,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1834,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_0,c_1079]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2231,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 28.00/4.00      inference(light_normalisation,
% 28.00/4.00                [status(thm)],
% 28.00/4.00                [c_2226,c_9,c_573,c_1834]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2716,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2231,c_11]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29759,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X3,X0),k4_xboole_0(X1,X2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1075,c_2716]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_29787,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_29759,c_2716]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30556,plain,
% 28.00/4.00      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30555,c_29787]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_5,plain,
% 28.00/4.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 28.00/4.00      inference(cnf_transformation,[],[f34]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_237,plain,
% 28.00/4.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 28.00/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3,plain,
% 28.00/4.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 28.00/4.00      | ~ r1_xboole_0(X1,X2) ),
% 28.00/4.00      inference(cnf_transformation,[],[f49]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_16,negated_conjecture,
% 28.00/4.00      ( r1_xboole_0(sK4,sK2) ),
% 28.00/4.00      inference(cnf_transformation,[],[f45]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_105,plain,
% 28.00/4.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 28.00/4.00      | sK2 != X2
% 28.00/4.00      | sK4 != X1 ),
% 28.00/4.00      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_106,plain,
% 28.00/4.00      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
% 28.00/4.00      inference(unflattening,[status(thm)],[c_105]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_234,plain,
% 28.00/4.00      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
% 28.00/4.00      inference(predicate_to_equality,[status(thm)],[c_106]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9948,plain,
% 28.00/4.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_237,c_234]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30557,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k1_xboole_0) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_30556,c_9948]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30558,plain,
% 28.00/4.00      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30557,c_6]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30659,plain,
% 28.00/4.00      ( k4_xboole_0(sK4,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,k4_xboole_0(sK5,sK4)) ),
% 28.00/4.00      inference(light_normalisation,
% 28.00/4.00                [status(thm)],
% 28.00/4.00                [c_30532,c_30196,c_30558]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_12870,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_2716]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_12989,plain,
% 28.00/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_12870,c_2716]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_30660,plain,
% 28.00/4.00      ( k4_xboole_0(sK4,sK2) = sK4 ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_30659,c_2231,c_12989]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_31360,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,sK4) = sK3 ),
% 28.00/4.00      inference(light_normalisation,
% 28.00/4.00                [status(thm)],
% 28.00/4.00                [c_29985,c_29985,c_30660]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_31374,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK4,X0)) = k2_xboole_0(sK3,X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_31360,c_13]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_576,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_243,c_10]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_6691,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(X0,k2_xboole_0(sK4,X1))) = k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK4,X1))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_992,c_576]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_33675,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))) = k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_31374,c_6691]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_33721,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_33675,c_31374]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_33722,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)),sK3) = k4_xboole_0(sK5,sK3) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_33721,c_31360]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_245,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2211,plain,
% 28.00/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_245,c_571]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_33723,plain,
% 28.00/4.00      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK5,sK3) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_33722,c_571,c_1177,c_2211]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_33616,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_518,c_31374]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1296,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_992,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_11211,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1296,c_1296]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1766,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_245,c_992]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_994,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_518,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_695,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_518,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9418,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,sK5))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_994,c_695]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9447,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) = k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_994,c_245]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_682,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_0,c_518]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2911,plain,
% 28.00/4.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_682,c_990]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2930,plain,
% 28.00/4.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_990,c_13]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_989,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2,c_244]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2771,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_989,c_13]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2800,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_2771,c_13]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2801,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2800,c_1177]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2961,plain,
% 28.00/4.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_2930,c_2801]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2962,plain,
% 28.00/4.00      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2961,c_990,c_2801]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2983,plain,
% 28.00/4.00      ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2911,c_2962]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2984,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_2983,c_1766]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3670,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X0)),X3)) = k2_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_566,c_245]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1715,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_8,c_245]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3697,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(X2,X3))) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_3670,c_1715,c_2801]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9490,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_9447,c_2984,c_3697]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9518,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_9418,c_9490]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2751,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_518,c_989]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2823,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2751,c_2801]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1343,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1282,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1013,plain,
% 28.00/4.00      ( k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_244,c_682]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1345,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_1343,c_1013]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_1765,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_245,c_1280]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2824,plain,
% 28.00/4.00      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_2823,c_1345,c_1765]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3051,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_1766,c_516]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_855,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_2,c_691]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_865,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_855,c_153]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_869,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK5,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_865,c_243]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2948,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.00      inference(superposition,[status(thm)],[c_990,c_869]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_2955,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.00      inference(demodulation,[status(thm)],[c_2948,c_990]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_3055,plain,
% 28.00/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_3051,c_153,c_2955]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_9519,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.00      inference(light_normalisation,[status(thm)],[c_9518,c_2824,c_3055]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_11227,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.00      inference(light_normalisation,
% 28.00/4.00                [status(thm)],
% 28.00/4.00                [c_11211,c_153,c_1766,c_9519]) ).
% 28.00/4.00  
% 28.00/4.00  cnf(c_12172,plain,
% 28.00/4.00      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_243,c_11227]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_24700,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1177,c_12172]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_24925,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_24700,c_1014,c_11227]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34371,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_33616,c_24925]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12158,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_516,c_11227]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_868,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK5,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_865,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1476,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK5,sK2),k4_xboole_0(sK3,k2_xboole_0(sK5,sK2))) = k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_868,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1001,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_865,c_244]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1477,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK2),sK3) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_1476,c_8,c_1001,c_1014]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1478,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK5,sK2),sK3) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_1477,c_2]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4093,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1478,c_13]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1864,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1079,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1867,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_1864,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_7971,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK5,k2_xboole_0(sK2,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_4093,c_1867]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8008,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_7971,c_4093]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12267,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_12158,c_8008]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34372,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_34371,c_12267]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34373,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_34372,c_1177]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_52452,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k2_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_11960,c_11960,c_33723,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_52476,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_52452,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1838,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_8,c_1079]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29567,plain,
% 28.00/4.01      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1838,c_1075]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2203,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_8,c_571]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2242,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_2203,c_571]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29994,plain,
% 28.00/4.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_29567,c_6,c_2242]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_725,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_682,c_243]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31565,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_29994,c_725]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31650,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_31565,c_153]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31904,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_31650,c_243]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34376,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_31904,c_31904,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34481,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34376,c_31374]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34484,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_34481,c_31650,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34828,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34484,c_989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34919,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k2_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_34828,c_34484]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45745,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,sK4)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34919,c_576]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1283,plain,
% 28.00/4.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_6,c_992]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_525,plain,
% 28.00/4.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1373,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1283,c_525]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_36635,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_1373,c_1373,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_36662,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_36635,c_576]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45759,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_45745,c_36662]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1843,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_153,c_1079]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29559,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1843,c_1075]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_30026,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = sK2 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_29559,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31709,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k2_xboole_0(sK2,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_30026,c_13]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40132,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_628,c_31709]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40303,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,sK5) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_40132,c_31709]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_15,negated_conjecture,
% 28.00/4.01      ( r1_xboole_0(sK5,sK3) ),
% 28.00/4.01      inference(cnf_transformation,[],[f46]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_96,plain,
% 28.00/4.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 28.00/4.01      | sK5 != X1
% 28.00/4.01      | sK3 != X2 ),
% 28.00/4.01      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_97,plain,
% 28.00/4.01      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
% 28.00/4.01      inference(unflattening,[status(thm)],[c_96]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_235,plain,
% 28.00/4.01      ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
% 28.00/4.01      inference(predicate_to_equality,[status(thm)],[c_97]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_620,plain,
% 28.00/4.01      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_1,c_235]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_9949,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_237,c_620]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40304,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK5) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_40303,c_9949]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40305,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,sK5) = sK2 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_40304,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1486,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK5,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_2,c_869]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1505,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_1486,c_865]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1603,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK5,sK2))) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1505,c_244]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1612,plain,
% 28.00/4.01      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_1603,c_865]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1635,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1612,c_518]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2464,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1635,c_571]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2479,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_2464,c_2208]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40358,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,sK4) = k4_xboole_0(sK2,sK4) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_40305,c_2479]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40542,plain,
% 28.00/4.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK2,sK4) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_40358,c_12]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40571,plain,
% 28.00/4.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_40542,c_40358]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_30535,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)),k4_xboole_0(sK5,sK4)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_30488,c_1]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_30656,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_30535,c_30196,c_30558]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_30657,plain,
% 28.00/4.01      ( k4_xboole_0(sK2,k4_xboole_0(sK5,sK4)) = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_30656,c_238,c_12989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40572,plain,
% 28.00/4.01      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_40571,c_30657]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40573,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,sK4) = sK2 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_40572,c_9]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41499,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k4_xboole_0(sK5,sK2)) = k4_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_40573,c_1095]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29569,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1856,c_1075]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4975,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1838,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4982,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_4975,c_6,c_2801]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_13026,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_516,c_4982]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2906,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_516,c_990]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2990,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_2906,c_990]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_13289,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_13026,c_10,c_2990]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_19405,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k2_xboole_0(sK2,sK3))) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_4093,c_13289]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1848,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_518,c_1079]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_3290,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,sK5),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_990,c_1848]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_3304,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_3290,c_525]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_7974,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_4093,c_990]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8005,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_7974,c_990,c_2801]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_19653,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_19405,c_3304,c_8005]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29990,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_29569,c_19653]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29991,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_29990,c_10,c_2984]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31576,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_29994,c_1766]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31629,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK4,X0))) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_31576,c_1373,c_29991]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35539,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK2,sK3) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_29991,c_31629,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2220,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_992,c_571]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4469,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k4_xboole_0(k2_xboole_0(sK4,k1_xboole_0),sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_990,c_2220]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4490,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_4469,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35548,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK5) = k4_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_35539,c_4490]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35552,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_35548,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40380,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,sK2) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_40305,c_1079]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_42268,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_41499,c_35552,c_40380]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_42269,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,sK5) = sK4 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_42268,c_9]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1064,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_48835,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,sK4),X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_42269,c_1064]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_49040,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k4_xboole_0(sK3,k2_xboole_0(sK4,X0)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_48835,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_52545,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK3,sK4) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_52476,c_2,c_45759,c_49040]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_88796,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_628,c_49040]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_88997,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK5)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_88796,c_49040]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_36660,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_36635,c_0]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1993,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k2_xboole_0(sK4,k2_xboole_0(X0,sK5))) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_518,c_1834]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1768,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_245,c_518]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2014,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_1993,c_1768]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12175,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_245,c_11227]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35612,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_35539,c_12175]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_33618,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_725,c_31374]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12170,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_245,c_11227]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34478,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK5,X1)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34376,c_12170]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31890,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X1) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_31650,c_13]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_5234,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_0,c_1867]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8078,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_245,c_5234]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2005,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1834,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2008,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_2005,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_5423,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X2,X1))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_566,c_2008]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_5531,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_5423,c_566,c_2801]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8254,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_8078,c_5531]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31931,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK5,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_31890,c_2984,c_8254]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34489,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_34478,c_31931,c_34373]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34434,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34376,c_1177]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34549,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_34434,c_34376]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35618,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_35612,c_1014,c_33618,c_34373,c_34489,c_34549]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40578,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_2014,c_2014,c_35618]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40611,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_992,c_40578]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_33619,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_682,c_31374]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_40720,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_40611,c_33619]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1008,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_244,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45840,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X0,X2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_29994,c_1008]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2774,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_989,c_1079]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46013,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_45840,c_11,c_2774]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46289,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k1_xboole_0,X3) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46013,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1227,plain,
% 28.00/4.01      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_525,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1244,plain,
% 28.00/4.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_1227,c_238]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46323,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_46289,c_11,c_1244,c_8254]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_49883,plain,
% 28.00/4.01      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_6,c_46323]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1106,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_12,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_11811,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_12,c_2104]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_11945,plain,
% 28.00/4.01      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_2104,c_243]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12094,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_11811,c_11945]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31549,plain,
% 28.00/4.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_29994,c_516]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31656,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_31549,c_29994]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54208,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_1106,c_1106,c_12094,c_31656]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54326,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_49883,c_54208]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46265,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_34484,c_46013]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1074,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_50608,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),sK3),k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46265,c_1074]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35723,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK3,sK5),X0) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_35552,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_35744,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_35723,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41497,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK4,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_40573,c_2716]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41491,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK2)) = k4_xboole_0(sK5,sK4) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_40573,c_12]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41546,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(sK5,sK2)) = sK2 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_41491,c_40573]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41547,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k1_xboole_0) = sK2 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_41546,c_40380]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_41548,plain,
% 28.00/4.01      ( sK2 = sK5 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_41547,c_9]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_42273,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_41497,c_35744,c_41548]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45485,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_35744,c_35744,c_42273]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45488,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k2_xboole_0(X0,sK5)) = k4_xboole_0(sK4,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_0,c_45485]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2702,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_11,c_2231]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_45616,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(sK4,X0)) = sK5 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_45488,c_2702]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_51003,plain,
% 28.00/4.01      ( k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_50608,c_6,c_11,c_238,c_45616]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46933,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46265,c_1075]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46935,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK5 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_46933,c_6,c_11]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_50664,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46935,c_1074]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_47537,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(X1,sK5)) = k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46935,c_2702]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_50948,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_50664,c_47537]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_50950,plain,
% 28.00/4.01      ( k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(X0,sK3)),k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sP0_iProver_split ),
% 28.00/4.01      inference(splitting,
% 28.00/4.01                [splitting(split),new_symbols(definition,[])],
% 28.00/4.01                [c_50948]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_51004,plain,
% 28.00/4.01      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = sP0_iProver_split ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_51003,c_50950]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54404,plain,
% 28.00/4.01      ( k2_xboole_0(sP0_iProver_split,k1_xboole_0) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_54326,c_51004]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54405,plain,
% 28.00/4.01      ( sP0_iProver_split = k1_xboole_0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_54404,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_61973,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_40720,c_40720,c_54405]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_61976,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_0,c_61973]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_63997,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK5,sK3))) = sP0_iProver_split ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_31360,c_61976]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31389,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK3) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_31360,c_1280]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_31399,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,sK3) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_31389,c_1177]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4243,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK4,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_3927,c_243]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_11969,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_2104,c_4243]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_11972,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_11969,c_3927]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12589,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_11972,c_518]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_33631,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_12589,c_31374]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_13983,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK4),sK5),sK4) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_12589,c_989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_3905,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1177,c_518]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_3926,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_3905,c_153,c_1282]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_14034,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK4),sK5),sK4) = k2_xboole_0(sK3,sK2) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_13983,c_3926]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_4766,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_573,c_573,c_2231]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_15709,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK2,sK4),sK5))) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_14034,c_4766]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_575,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_153,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_633,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_575,c_1]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_7473,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_633,c_633,c_1843]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_7474,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_7473,c_9,c_633]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_15744,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = sK5 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_15709,c_2716,c_7474]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_33754,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK5) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_33631,c_15744]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_64184,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_63997,c_31399,c_33754]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_88998,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,k2_xboole_0(sK4,k1_xboole_0)) = sP0_iProver_split ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_88997,c_9949,c_36660,c_64184]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54504,plain,
% 28.00/4.01      ( k2_xboole_0(X0,sP0_iProver_split) = X0 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_54405,c_6]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_88999,plain,
% 28.00/4.01      ( k4_xboole_0(sK3,sK4) = sP0_iProver_split ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_88998,c_54405,c_54504]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_93628,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = sP0_iProver_split ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_52545,c_52545,c_88999]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_93696,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,sK3))) = k2_xboole_0(sK4,sP0_iProver_split) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_93628,c_1075]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_51207,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),sK4),k2_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),sK4),k4_xboole_0(sK4,k1_xboole_0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_51003,c_628]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2740,plain,
% 28.00/4.01      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_8,c_989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2830,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_2740,c_989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_51229,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,sK3),sK4) = k2_xboole_0(X0,sK3) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_51207,c_9,c_2830,c_31656]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46295,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X2),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k2_xboole_0(X0,X1)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46013,c_628]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46316,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(X0,k2_xboole_0(X2,k1_xboole_0))) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_46295,c_11,c_31656]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_46317,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_46316,c_6,c_2830]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_49570,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_46317,c_0]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_53805,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_0,c_49570]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_56896,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK4,k2_xboole_0(X1,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_51229,c_53805]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_51328,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(sK3,X0),sK4) = k2_xboole_0(X0,sK3) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_0,c_51229]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_56899,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK4,k2_xboole_0(sK3,X1)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_51328,c_53805]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_53759,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_42269,c_49570]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_57003,plain,
% 28.00/4.01      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(X1,sK3)) = k2_xboole_0(sK3,X1) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_56899,c_53759]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_57007,plain,
% 28.00/4.01      ( k2_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_56896,c_57003]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29047,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_991,c_992]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_29132,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_29047,c_1014]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34319,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_33616,c_1177]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34321,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_33616,c_989]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8095,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_869,c_5234]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2918,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_869,c_990]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_2974,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,sK2)),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_2918,c_2962]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_8240,plain,
% 28.00/4.01      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_8095,c_2974]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34649,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(X0,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_34321,c_8240]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34651,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_34319,c_34649]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34374,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_34373,c_33616]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_34652,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_34651,c_33619,c_34373,c_34374]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_82319,plain,
% 28.00/4.01      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK3))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_29132,c_29132,c_34652]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1189,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_13,c_10]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_82374,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK5,sK4),k4_xboole_0(X0,sK3)) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_82319,c_1189]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_82469,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,sK3)) ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_82374,c_36635]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12942,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_2716,c_4766]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12953,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_12942,c_8254]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_12954,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_12953,c_8]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_82470,plain,
% 28.00/4.01      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK5,X0),sK3) ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_82469,c_12954]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_93700,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,k4_xboole_0(sK5,sK5)) = sK4 ),
% 28.00/4.01      inference(demodulation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_93696,c_54504,c_57007,c_82470]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_7147,plain,
% 28.00/4.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_13,c_2702]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_13399,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = sK5 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1768,c_7147]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54810,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK5,X1)))) = sK5 ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_13399,c_13399,c_41548]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54868,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k4_xboole_0(sK5,sK5) ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_54810,c_12]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_3034,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
% 28.00/4.01      inference(superposition,[status(thm)],[c_1766,c_1834]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_42525,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = k1_xboole_0 ),
% 28.00/4.01      inference(light_normalisation,
% 28.00/4.01                [status(thm)],
% 28.00/4.01                [c_3034,c_3034,c_35618]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54489,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK5,X0))) = sP0_iProver_split ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_54405,c_42525]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_54894,plain,
% 28.00/4.01      ( k4_xboole_0(sK5,sK5) = sP0_iProver_split ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_54868,c_54489]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_93701,plain,
% 28.00/4.01      ( k2_xboole_0(sK3,sP0_iProver_split) = sK4 ),
% 28.00/4.01      inference(light_normalisation,[status(thm)],[c_93700,c_54894]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_93702,plain,
% 28.00/4.01      ( sK4 = sK3 ),
% 28.00/4.01      inference(demodulation,[status(thm)],[c_93701,c_54504]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_155,plain,( X0 = X0 ),theory(equality) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_1130,plain,
% 28.00/4.01      ( sK3 = sK3 ),
% 28.00/4.01      inference(instantiation,[status(thm)],[c_155]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_156,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_249,plain,
% 28.00/4.01      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 28.00/4.01      inference(instantiation,[status(thm)],[c_156]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_463,plain,
% 28.00/4.01      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 28.00/4.01      inference(instantiation,[status(thm)],[c_249]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(c_14,negated_conjecture,
% 28.00/4.01      ( sK3 != sK4 ),
% 28.00/4.01      inference(cnf_transformation,[],[f47]) ).
% 28.00/4.01  
% 28.00/4.01  cnf(contradiction,plain,
% 28.00/4.01      ( $false ),
% 28.00/4.01      inference(minisat,[status(thm)],[c_93702,c_1130,c_463,c_14]) ).
% 28.00/4.01  
% 28.00/4.01  
% 28.00/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 28.00/4.01  
% 28.00/4.01  ------                               Statistics
% 28.00/4.01  
% 28.00/4.01  ------ General
% 28.00/4.01  
% 28.00/4.01  abstr_ref_over_cycles:                  0
% 28.00/4.01  abstr_ref_under_cycles:                 0
% 28.00/4.01  gc_basic_clause_elim:                   0
% 28.00/4.01  forced_gc_time:                         0
% 28.00/4.01  parsing_time:                           0.008
% 28.00/4.01  unif_index_cands_time:                  0.
% 28.00/4.01  unif_index_add_time:                    0.
% 28.00/4.01  orderings_time:                         0.
% 28.00/4.01  out_proof_time:                         0.019
% 28.00/4.01  total_time:                             3.373
% 28.00/4.01  num_of_symbols:                         44
% 28.00/4.01  num_of_terms:                           155240
% 28.00/4.01  
% 28.00/4.01  ------ Preprocessing
% 28.00/4.01  
% 28.00/4.01  num_of_splits:                          0
% 28.00/4.01  num_of_split_atoms:                     2
% 28.00/4.01  num_of_reused_defs:                     0
% 28.00/4.01  num_eq_ax_congr_red:                    9
% 28.00/4.01  num_of_sem_filtered_clauses:            1
% 28.00/4.01  num_of_subtypes:                        0
% 28.00/4.01  monotx_restored_types:                  0
% 28.00/4.01  sat_num_of_epr_types:                   0
% 28.00/4.01  sat_num_of_non_cyclic_types:            0
% 28.00/4.01  sat_guarded_non_collapsed_types:        0
% 28.00/4.01  num_pure_diseq_elim:                    0
% 28.00/4.01  simp_replaced_by:                       0
% 28.00/4.01  res_preprocessed:                       80
% 28.00/4.01  prep_upred:                             0
% 28.00/4.01  prep_unflattend:                        6
% 28.00/4.01  smt_new_axioms:                         0
% 28.00/4.01  pred_elim_cands:                        1
% 28.00/4.01  pred_elim:                              1
% 28.00/4.01  pred_elim_cl:                           1
% 28.00/4.01  pred_elim_cycles:                       3
% 28.00/4.01  merged_defs:                            0
% 28.00/4.01  merged_defs_ncl:                        0
% 28.00/4.01  bin_hyper_res:                          0
% 28.00/4.01  prep_cycles:                            4
% 28.00/4.01  pred_elim_time:                         0.
% 28.00/4.01  splitting_time:                         0.
% 28.00/4.01  sem_filter_time:                        0.
% 28.00/4.01  monotx_time:                            0.
% 28.00/4.01  subtype_inf_time:                       0.
% 28.00/4.01  
% 28.00/4.01  ------ Problem properties
% 28.00/4.01  
% 28.00/4.01  clauses:                                17
% 28.00/4.01  conjectures:                            2
% 28.00/4.01  epr:                                    1
% 28.00/4.01  horn:                                   16
% 28.00/4.01  ground:                                 2
% 28.00/4.01  unary:                                  15
% 28.00/4.01  binary:                                 2
% 28.00/4.01  lits:                                   19
% 28.00/4.01  lits_eq:                                14
% 28.00/4.01  fd_pure:                                0
% 28.00/4.01  fd_pseudo:                              0
% 28.00/4.01  fd_cond:                                1
% 28.00/4.01  fd_pseudo_cond:                         0
% 28.00/4.01  ac_symbols:                             1
% 28.00/4.01  
% 28.00/4.01  ------ Propositional Solver
% 28.00/4.01  
% 28.00/4.01  prop_solver_calls:                      37
% 28.00/4.01  prop_fast_solver_calls:                 1162
% 28.00/4.01  smt_solver_calls:                       0
% 28.00/4.01  smt_fast_solver_calls:                  0
% 28.00/4.01  prop_num_of_clauses:                    23345
% 28.00/4.01  prop_preprocess_simplified:             16114
% 28.00/4.01  prop_fo_subsumed:                       0
% 28.00/4.01  prop_solver_time:                       0.
% 28.00/4.01  smt_solver_time:                        0.
% 28.00/4.01  smt_fast_solver_time:                   0.
% 28.00/4.01  prop_fast_solver_time:                  0.
% 28.00/4.01  prop_unsat_core_time:                   0.002
% 28.00/4.01  
% 28.00/4.01  ------ QBF
% 28.00/4.01  
% 28.00/4.01  qbf_q_res:                              0
% 28.00/4.01  qbf_num_tautologies:                    0
% 28.00/4.01  qbf_prep_cycles:                        0
% 28.00/4.01  
% 28.00/4.01  ------ BMC1
% 28.00/4.01  
% 28.00/4.01  bmc1_current_bound:                     -1
% 28.00/4.01  bmc1_last_solved_bound:                 -1
% 28.00/4.01  bmc1_unsat_core_size:                   -1
% 28.00/4.01  bmc1_unsat_core_parents_size:           -1
% 28.00/4.01  bmc1_merge_next_fun:                    0
% 28.00/4.01  bmc1_unsat_core_clauses_time:           0.
% 28.00/4.01  
% 28.00/4.01  ------ Instantiation
% 28.00/4.01  
% 28.00/4.01  inst_num_of_clauses:                    5174
% 28.00/4.01  inst_num_in_passive:                    1653
% 28.00/4.01  inst_num_in_active:                     1552
% 28.00/4.01  inst_num_in_unprocessed:                1969
% 28.00/4.01  inst_num_of_loops:                      2190
% 28.00/4.01  inst_num_of_learning_restarts:          0
% 28.00/4.01  inst_num_moves_active_passive:          634
% 28.00/4.01  inst_lit_activity:                      0
% 28.00/4.01  inst_lit_activity_moves:                1
% 28.00/4.01  inst_num_tautologies:                   0
% 28.00/4.01  inst_num_prop_implied:                  0
% 28.00/4.01  inst_num_existing_simplified:           0
% 28.00/4.01  inst_num_eq_res_simplified:             0
% 28.00/4.01  inst_num_child_elim:                    0
% 28.00/4.01  inst_num_of_dismatching_blockings:      2543
% 28.00/4.01  inst_num_of_non_proper_insts:           4487
% 28.00/4.01  inst_num_of_duplicates:                 0
% 28.00/4.01  inst_inst_num_from_inst_to_res:         0
% 28.00/4.01  inst_dismatching_checking_time:         0.
% 28.00/4.01  
% 28.00/4.01  ------ Resolution
% 28.00/4.01  
% 28.00/4.01  res_num_of_clauses:                     0
% 28.00/4.01  res_num_in_passive:                     0
% 28.00/4.01  res_num_in_active:                      0
% 28.00/4.01  res_num_of_loops:                       84
% 28.00/4.01  res_forward_subset_subsumed:            880
% 28.00/4.01  res_backward_subset_subsumed:           2
% 28.00/4.01  res_forward_subsumed:                   0
% 28.00/4.01  res_backward_subsumed:                  0
% 28.00/4.01  res_forward_subsumption_resolution:     0
% 28.00/4.01  res_backward_subsumption_resolution:    0
% 28.00/4.01  res_clause_to_clause_subsumption:       163702
% 28.00/4.01  res_orphan_elimination:                 0
% 28.00/4.01  res_tautology_del:                      355
% 28.00/4.01  res_num_eq_res_simplified:              0
% 28.00/4.01  res_num_sel_changes:                    0
% 28.00/4.01  res_moves_from_active_to_pass:          0
% 28.00/4.01  
% 28.00/4.01  ------ Superposition
% 28.00/4.01  
% 28.00/4.01  sup_time_total:                         0.
% 28.00/4.01  sup_time_generating:                    0.
% 28.00/4.01  sup_time_sim_full:                      0.
% 28.00/4.01  sup_time_sim_immed:                     0.
% 28.00/4.01  
% 28.00/4.01  sup_num_of_clauses:                     8907
% 28.00/4.01  sup_num_in_active:                      185
% 28.00/4.01  sup_num_in_passive:                     8722
% 28.00/4.01  sup_num_of_loops:                       436
% 28.00/4.01  sup_fw_superposition:                   18275
% 28.00/4.01  sup_bw_superposition:                   17542
% 28.00/4.01  sup_immediate_simplified:               24445
% 28.00/4.01  sup_given_eliminated:                   14
% 28.00/4.01  comparisons_done:                       0
% 28.00/4.01  comparisons_avoided:                    0
% 28.00/4.01  
% 28.00/4.01  ------ Simplifications
% 28.00/4.01  
% 28.00/4.01  
% 28.00/4.01  sim_fw_subset_subsumed:                 0
% 28.00/4.01  sim_bw_subset_subsumed:                 0
% 28.00/4.01  sim_fw_subsumed:                        2654
% 28.00/4.01  sim_bw_subsumed:                        165
% 28.00/4.01  sim_fw_subsumption_res:                 0
% 28.00/4.01  sim_bw_subsumption_res:                 0
% 28.00/4.01  sim_tautology_del:                      0
% 28.00/4.01  sim_eq_tautology_del:                   6111
% 28.00/4.01  sim_eq_res_simp:                        0
% 28.00/4.01  sim_fw_demodulated:                     18216
% 28.00/4.01  sim_bw_demodulated:                     471
% 28.00/4.01  sim_light_normalised:                   10711
% 28.00/4.01  sim_joinable_taut:                      742
% 28.00/4.01  sim_joinable_simp:                      0
% 28.00/4.01  sim_ac_normalised:                      0
% 28.00/4.01  sim_smt_subsumption:                    0
% 28.00/4.01  
%------------------------------------------------------------------------------
