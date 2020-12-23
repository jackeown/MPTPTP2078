%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:42 EST 2020

% Result     : Theorem 51.43s
% Output     : CNFRefutation 51.43s
% Verified   : 
% Statistics : Number of formulae       :  306 (11392 expanded)
%              Number of clauses        :  255 (5165 expanded)
%              Number of leaves         :   21 (2880 expanded)
%              Depth                    :   37
%              Number of atoms          :  416 (13608 expanded)
%              Number of equality atoms :  331 (12073 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK2 != sK4
      & r1_xboole_0(sK4,sK3)
      & r1_xboole_0(sK2,sK3)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29])).

fof(f47,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f49,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_342,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_10])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1281,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_342,c_11])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1294,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1281,c_6])).

cnf(c_2348,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_18,c_1294])).

cnf(c_2376,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_2348,c_1294])).

cnf(c_13,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2518,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_2376,c_13])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_729,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_1179,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_729])).

cnf(c_1415,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1179,c_11])).

cnf(c_1416,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1415,c_6])).

cnf(c_6841,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2518,c_1416])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7928,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK2,k4_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_6841,c_9])).

cnf(c_7934,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_7928,c_9])).

cnf(c_1178,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_729])).

cnf(c_2149,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1178])).

cnf(c_4195,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2149,c_11])).

cnf(c_4199,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_4195,c_6])).

cnf(c_219579,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)))) ),
    inference(superposition,[status(thm)],[c_7934,c_4199])).

cnf(c_883,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_2860,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_883,c_9])).

cnf(c_2522,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(sK2,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_2376,c_11])).

cnf(c_3863,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_2522,c_11])).

cnf(c_6378,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),sK3) = k4_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_2860,c_3863])).

cnf(c_6414,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_6378,c_2376])).

cnf(c_1285,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_6464,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),sK3),k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6414,c_1285])).

cnf(c_7715,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6464,c_9])).

cnf(c_3862,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_2522,c_0])).

cnf(c_3970,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_3862,c_3863])).

cnf(c_7723,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_7715,c_6,c_3970])).

cnf(c_1187,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_729,c_9])).

cnf(c_1191,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1187,c_6])).

cnf(c_2319,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_18,c_1191])).

cnf(c_2337,plain,
    ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_2319,c_1191])).

cnf(c_6834,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_11,c_1416])).

cnf(c_56193,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),sK3) = k4_xboole_0(k4_xboole_0(sK4,X0),sK3) ),
    inference(superposition,[status(thm)],[c_2337,c_6834])).

cnf(c_56427,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k4_xboole_0(sK4,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_56193,c_6834])).

cnf(c_60779,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7723,c_7723,c_56427])).

cnf(c_219631,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))),k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))) ),
    inference(superposition,[status(thm)],[c_60779,c_4199])).

cnf(c_2838,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = sK4 ),
    inference(superposition,[status(thm)],[c_2376,c_883])).

cnf(c_1282,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_729,c_11])).

cnf(c_1293,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_1282,c_6])).

cnf(c_10676,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1293,c_9])).

cnf(c_10700,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_10676,c_9])).

cnf(c_78773,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_9,c_10700])).

cnf(c_2172,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1178,c_9])).

cnf(c_2181,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2172,c_6])).

cnf(c_78803,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2181,c_10700])).

cnf(c_78914,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2860,c_10700])).

cnf(c_739,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_9])).

cnf(c_743,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_739,c_6])).

cnf(c_2099,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_743])).

cnf(c_79621,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_78914,c_2099])).

cnf(c_79815,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_78803,c_79621])).

cnf(c_1275,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_342,c_11])).

cnf(c_677,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1300,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1275,c_677])).

cnf(c_6889,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1416,c_9])).

cnf(c_6907,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6889,c_9])).

cnf(c_18620,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1300,c_6907])).

cnf(c_79017,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_10700,c_743])).

cnf(c_79033,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_10700,c_0])).

cnf(c_79111,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_79017,c_79033])).

cnf(c_2314,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1191])).

cnf(c_79112,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_79111,c_2314])).

cnf(c_79816,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_79815,c_18620,c_79112])).

cnf(c_79861,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_78773,c_79816])).

cnf(c_79862,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_79861,c_9])).

cnf(c_83048,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2838,c_79862])).

cnf(c_219661,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK4,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) ),
    inference(superposition,[status(thm)],[c_83048,c_4199])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_341,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_123,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_336,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_2510,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2376,c_336])).

cnf(c_6817,plain,
    ( v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_341,c_2510])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_132,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_335,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_6814,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_341,c_335])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_338,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_202995,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6814,c_338])).

cnf(c_203324,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_6817,c_202995])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_339,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_203322,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_339,c_202995])).

cnf(c_203621,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_203324,c_203322])).

cnf(c_220008,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK4,X1)) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_219661,c_203621])).

cnf(c_989,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_677,c_12])).

cnf(c_2327,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1191,c_0])).

cnf(c_1413,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1179,c_9])).

cnf(c_1419,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1413,c_6])).

cnf(c_732,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_12])).

cnf(c_1277,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_732,c_11])).

cnf(c_1298,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1277,c_677])).

cnf(c_1566,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1419,c_1298])).

cnf(c_1581,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1566,c_732])).

cnf(c_1659,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK4,X1)),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1581,c_11])).

cnf(c_1660,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK4,X1)),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1659,c_6])).

cnf(c_17220,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),k2_xboole_0(sK2,sK3)) = k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2860,c_1660])).

cnf(c_17289,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17220,c_1581])).

cnf(c_1283,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_732,c_11])).

cnf(c_1292,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1283,c_6])).

cnf(c_1536,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1292,c_1419])).

cnf(c_1988,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_0,c_1536])).

cnf(c_42148,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) ),
    inference(superposition,[status(thm)],[c_17289,c_1988])).

cnf(c_1571,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1298,c_13])).

cnf(c_41894,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),k1_xboole_0),k1_xboole_0) = k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
    inference(superposition,[status(thm)],[c_17289,c_1571])).

cnf(c_5026,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1285,c_9])).

cnf(c_2103,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_743])).

cnf(c_1288,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_2132,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(demodulation,[status(thm)],[c_2103,c_1288])).

cnf(c_5036,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_5026,c_2132])).

cnf(c_3084,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2099,c_12])).

cnf(c_5274,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3084,c_9])).

cnf(c_2117,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_743,c_0])).

cnf(c_4255,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2314,c_2117])).

cnf(c_4277,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_4255,c_2314])).

cnf(c_5288,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5274,c_4277])).

cnf(c_7952,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_10,c_1288])).

cnf(c_8126,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7952,c_10])).

cnf(c_18607,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2860,c_6907])).

cnf(c_18801,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_18607,c_1419])).

cnf(c_42004,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)) = sK4 ),
    inference(demodulation,[status(thm)],[c_41894,c_5036,c_5288,c_8126,c_18801])).

cnf(c_42250,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_42148,c_42004])).

cnf(c_42251,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_42250,c_6])).

cnf(c_2517,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK4,X0),sK3) ),
    inference(superposition,[status(thm)],[c_2376,c_11])).

cnf(c_3838,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(sK4,X0),sK3) ),
    inference(superposition,[status(thm)],[c_2517,c_11])).

cnf(c_6173,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_0,c_3838])).

cnf(c_42662,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),sK3) = k4_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_42251,c_6173])).

cnf(c_42681,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_42662,c_2376])).

cnf(c_1280,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_1295,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1280,c_6])).

cnf(c_12788,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2327,c_1295])).

cnf(c_12975,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12788,c_12])).

cnf(c_13281,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X0),X1),X3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_12975])).

cnf(c_103696,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK3),k2_xboole_0(k4_xboole_0(sK2,sK3),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_42681,c_13281])).

cnf(c_134132,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(k4_xboole_0(sK2,sK3),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2376,c_103696])).

cnf(c_134344,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2327,c_134132])).

cnf(c_4362,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_2327])).

cnf(c_4410,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_4362,c_9])).

cnf(c_11341,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4410])).

cnf(c_151796,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3)) ),
    inference(superposition,[status(thm)],[c_134344,c_11341])).

cnf(c_151821,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_134344,c_9])).

cnf(c_83226,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_79862,c_2327])).

cnf(c_83347,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_83226,c_79862])).

cnf(c_8265,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8126,c_1288])).

cnf(c_8274,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_8265,c_8126])).

cnf(c_8275,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8274,c_10])).

cnf(c_83231,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X3,X2),X0)) ),
    inference(superposition,[status(thm)],[c_79862,c_8275])).

cnf(c_83345,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_83231,c_79862])).

cnf(c_83348,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2)))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_83347,c_83345])).

cnf(c_4264,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2314,c_0])).

cnf(c_8266,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_8126,c_11])).

cnf(c_8272,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_8266,c_8126])).

cnf(c_8273,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8272,c_10])).

cnf(c_20786,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_8273,c_2327])).

cnf(c_83349,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_83348,c_4264,c_20786])).

cnf(c_151849,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_151821,c_5288,c_83349])).

cnf(c_2352,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1294,c_1419])).

cnf(c_138656,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2352])).

cnf(c_151817,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3),k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_134344,c_138656])).

cnf(c_151853,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK3),X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_151817,c_151849])).

cnf(c_1276,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_729,c_11])).

cnf(c_1299,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_1276,c_677])).

cnf(c_14834,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1299,c_9])).

cnf(c_14866,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_14834,c_9])).

cnf(c_12867,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1295,c_9])).

cnf(c_12892,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_12867,c_9])).

cnf(c_79074,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_10700,c_8273])).

cnf(c_10615,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_1293])).

cnf(c_8348,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2181])).

cnf(c_73147,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10615,c_8348])).

cnf(c_24336,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1293,c_8348])).

cnf(c_24562,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24336,c_10700])).

cnf(c_24563,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_24562,c_10700])).

cnf(c_73340,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_73147,c_14866,c_24563])).

cnf(c_79431,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_79074,c_73340,c_79112])).

cnf(c_97338,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_12892,c_79431,c_83349])).

cnf(c_97690,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_97338,c_0])).

cnf(c_110529,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_14866,c_83349,c_97690])).

cnf(c_110716,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_11,c_110529])).

cnf(c_78905,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_1288,c_10700])).

cnf(c_79626,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(demodulation,[status(thm)],[c_78905,c_1288,c_79112])).

cnf(c_111267,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,X3),X1)) ),
    inference(light_normalisation,[status(thm)],[c_110716,c_79626])).

cnf(c_151854,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k2_xboole_0(X1,k4_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_151853,c_5288,c_111267])).

cnf(c_151866,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_151796,c_151849,c_151854])).

cnf(c_220009,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK3),X1)) = k4_xboole_0(X0,k2_xboole_0(sK4,X1)) ),
    inference(demodulation,[status(thm)],[c_220008,c_6,c_989,c_151866])).

cnf(c_220046,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))),k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X1),sK3))) ),
    inference(demodulation,[status(thm)],[c_219631,c_220009])).

cnf(c_56634,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_56427,c_17289])).

cnf(c_1567,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1298,c_1419])).

cnf(c_9176,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1567])).

cnf(c_64237,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK4),k1_xboole_0) = k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) ),
    inference(superposition,[status(thm)],[c_56634,c_9176])).

cnf(c_56631,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_56427,c_42251])).

cnf(c_64343,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_64237,c_56631])).

cnf(c_64344,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_64343,c_6])).

cnf(c_220047,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,sK4) ),
    inference(demodulation,[status(thm)],[c_220046,c_1416,c_64344])).

cnf(c_220108,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK4,sK4))),k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK4,sK4))) ),
    inference(demodulation,[status(thm)],[c_219579,c_220047])).

cnf(c_12781,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_2860,c_1295])).

cnf(c_12982,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12781,c_12])).

cnf(c_15265,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X3)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12982,c_11])).

cnf(c_15286,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_15265,c_6])).

cnf(c_220109,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_220108,c_6,c_342,c_15286])).

cnf(c_2152,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_1178])).

cnf(c_221083,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK2),sK2),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_220109,c_2152])).

cnf(c_16579,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_9,c_1300])).

cnf(c_16683,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_16579,c_1300])).

cnf(c_221334,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_221083,c_16683])).

cnf(c_202996,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6817,c_338])).

cnf(c_203002,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_202996])).

cnf(c_206,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_704,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_46709,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,sK3) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_202,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_840,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_9693,plain,
    ( k4_xboole_0(sK4,sK2) != X0
    | k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_9694,plain,
    ( k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK4,sK2) != k1_xboole_0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9693])).

cnf(c_383,plain,
    ( k4_xboole_0(sK4,sK2) != X0
    | k4_xboole_0(sK2,sK4) != X0
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_480,plain,
    ( k4_xboole_0(sK4,sK2) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_7593,plain,
    ( k4_xboole_0(sK4,sK2) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_201,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4095,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) = k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_3816,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_661,plain,
    ( X0 != X1
    | k4_xboole_0(sK2,sK4) != X1
    | k4_xboole_0(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1461,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
    | k4_xboole_0(sK2,sK4) != X0
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_2676,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_2516,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2376,c_1179])).

cnf(c_8,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2586,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) != k1_xboole_0
    | k4_xboole_0(sK2,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_2516,c_8])).

cnf(c_653,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),X0) != k4_xboole_0(X0,k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1974,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) != k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4))
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_483,plain,
    ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1938,plain,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1203,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_502,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_423,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_425,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_352,plain,
    ( k4_xboole_0(sK2,sK4) != k4_xboole_0(sK4,sK2)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_38,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_221334,c_203002,c_46709,c_9694,c_7593,c_4095,c_3816,c_2676,c_2586,c_1974,c_1938,c_1203,c_502,c_425,c_352,c_38,c_3,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 51.43/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.43/7.00  
% 51.43/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.43/7.00  
% 51.43/7.00  ------  iProver source info
% 51.43/7.00  
% 51.43/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.43/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.43/7.00  git: non_committed_changes: false
% 51.43/7.00  git: last_make_outside_of_git: false
% 51.43/7.00  
% 51.43/7.00  ------ 
% 51.43/7.00  
% 51.43/7.00  ------ Input Options
% 51.43/7.00  
% 51.43/7.00  --out_options                           all
% 51.43/7.00  --tptp_safe_out                         true
% 51.43/7.00  --problem_path                          ""
% 51.43/7.00  --include_path                          ""
% 51.43/7.00  --clausifier                            res/vclausify_rel
% 51.43/7.00  --clausifier_options                    ""
% 51.43/7.00  --stdin                                 false
% 51.43/7.00  --stats_out                             all
% 51.43/7.00  
% 51.43/7.00  ------ General Options
% 51.43/7.00  
% 51.43/7.00  --fof                                   false
% 51.43/7.00  --time_out_real                         305.
% 51.43/7.00  --time_out_virtual                      -1.
% 51.43/7.00  --symbol_type_check                     false
% 51.43/7.00  --clausify_out                          false
% 51.43/7.00  --sig_cnt_out                           false
% 51.43/7.00  --trig_cnt_out                          false
% 51.43/7.00  --trig_cnt_out_tolerance                1.
% 51.43/7.00  --trig_cnt_out_sk_spl                   false
% 51.43/7.00  --abstr_cl_out                          false
% 51.43/7.00  
% 51.43/7.00  ------ Global Options
% 51.43/7.00  
% 51.43/7.00  --schedule                              default
% 51.43/7.00  --add_important_lit                     false
% 51.43/7.00  --prop_solver_per_cl                    1000
% 51.43/7.00  --min_unsat_core                        false
% 51.43/7.00  --soft_assumptions                      false
% 51.43/7.00  --soft_lemma_size                       3
% 51.43/7.00  --prop_impl_unit_size                   0
% 51.43/7.00  --prop_impl_unit                        []
% 51.43/7.00  --share_sel_clauses                     true
% 51.43/7.00  --reset_solvers                         false
% 51.43/7.00  --bc_imp_inh                            [conj_cone]
% 51.43/7.00  --conj_cone_tolerance                   3.
% 51.43/7.00  --extra_neg_conj                        none
% 51.43/7.00  --large_theory_mode                     true
% 51.43/7.00  --prolific_symb_bound                   200
% 51.43/7.00  --lt_threshold                          2000
% 51.43/7.00  --clause_weak_htbl                      true
% 51.43/7.00  --gc_record_bc_elim                     false
% 51.43/7.00  
% 51.43/7.00  ------ Preprocessing Options
% 51.43/7.00  
% 51.43/7.00  --preprocessing_flag                    true
% 51.43/7.00  --time_out_prep_mult                    0.1
% 51.43/7.00  --splitting_mode                        input
% 51.43/7.00  --splitting_grd                         true
% 51.43/7.00  --splitting_cvd                         false
% 51.43/7.00  --splitting_cvd_svl                     false
% 51.43/7.00  --splitting_nvd                         32
% 51.43/7.00  --sub_typing                            true
% 51.43/7.00  --prep_gs_sim                           true
% 51.43/7.00  --prep_unflatten                        true
% 51.43/7.00  --prep_res_sim                          true
% 51.43/7.00  --prep_upred                            true
% 51.43/7.00  --prep_sem_filter                       exhaustive
% 51.43/7.00  --prep_sem_filter_out                   false
% 51.43/7.00  --pred_elim                             true
% 51.43/7.00  --res_sim_input                         true
% 51.43/7.00  --eq_ax_congr_red                       true
% 51.43/7.00  --pure_diseq_elim                       true
% 51.43/7.00  --brand_transform                       false
% 51.43/7.00  --non_eq_to_eq                          false
% 51.43/7.00  --prep_def_merge                        true
% 51.43/7.00  --prep_def_merge_prop_impl              false
% 51.43/7.00  --prep_def_merge_mbd                    true
% 51.43/7.00  --prep_def_merge_tr_red                 false
% 51.43/7.00  --prep_def_merge_tr_cl                  false
% 51.43/7.00  --smt_preprocessing                     true
% 51.43/7.00  --smt_ac_axioms                         fast
% 51.43/7.00  --preprocessed_out                      false
% 51.43/7.00  --preprocessed_stats                    false
% 51.43/7.00  
% 51.43/7.00  ------ Abstraction refinement Options
% 51.43/7.00  
% 51.43/7.00  --abstr_ref                             []
% 51.43/7.00  --abstr_ref_prep                        false
% 51.43/7.00  --abstr_ref_until_sat                   false
% 51.43/7.00  --abstr_ref_sig_restrict                funpre
% 51.43/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.43/7.00  --abstr_ref_under                       []
% 51.43/7.00  
% 51.43/7.00  ------ SAT Options
% 51.43/7.00  
% 51.43/7.00  --sat_mode                              false
% 51.43/7.00  --sat_fm_restart_options                ""
% 51.43/7.00  --sat_gr_def                            false
% 51.43/7.00  --sat_epr_types                         true
% 51.43/7.00  --sat_non_cyclic_types                  false
% 51.43/7.00  --sat_finite_models                     false
% 51.43/7.00  --sat_fm_lemmas                         false
% 51.43/7.00  --sat_fm_prep                           false
% 51.43/7.00  --sat_fm_uc_incr                        true
% 51.43/7.00  --sat_out_model                         small
% 51.43/7.00  --sat_out_clauses                       false
% 51.43/7.00  
% 51.43/7.00  ------ QBF Options
% 51.43/7.00  
% 51.43/7.00  --qbf_mode                              false
% 51.43/7.00  --qbf_elim_univ                         false
% 51.43/7.00  --qbf_dom_inst                          none
% 51.43/7.00  --qbf_dom_pre_inst                      false
% 51.43/7.00  --qbf_sk_in                             false
% 51.43/7.00  --qbf_pred_elim                         true
% 51.43/7.00  --qbf_split                             512
% 51.43/7.00  
% 51.43/7.00  ------ BMC1 Options
% 51.43/7.00  
% 51.43/7.00  --bmc1_incremental                      false
% 51.43/7.00  --bmc1_axioms                           reachable_all
% 51.43/7.00  --bmc1_min_bound                        0
% 51.43/7.00  --bmc1_max_bound                        -1
% 51.43/7.00  --bmc1_max_bound_default                -1
% 51.43/7.00  --bmc1_symbol_reachability              true
% 51.43/7.00  --bmc1_property_lemmas                  false
% 51.43/7.00  --bmc1_k_induction                      false
% 51.43/7.00  --bmc1_non_equiv_states                 false
% 51.43/7.00  --bmc1_deadlock                         false
% 51.43/7.00  --bmc1_ucm                              false
% 51.43/7.00  --bmc1_add_unsat_core                   none
% 51.43/7.00  --bmc1_unsat_core_children              false
% 51.43/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.43/7.00  --bmc1_out_stat                         full
% 51.43/7.00  --bmc1_ground_init                      false
% 51.43/7.00  --bmc1_pre_inst_next_state              false
% 51.43/7.00  --bmc1_pre_inst_state                   false
% 51.43/7.00  --bmc1_pre_inst_reach_state             false
% 51.43/7.00  --bmc1_out_unsat_core                   false
% 51.43/7.00  --bmc1_aig_witness_out                  false
% 51.43/7.00  --bmc1_verbose                          false
% 51.43/7.00  --bmc1_dump_clauses_tptp                false
% 51.43/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.43/7.00  --bmc1_dump_file                        -
% 51.43/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.43/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.43/7.00  --bmc1_ucm_extend_mode                  1
% 51.43/7.00  --bmc1_ucm_init_mode                    2
% 51.43/7.00  --bmc1_ucm_cone_mode                    none
% 51.43/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.43/7.00  --bmc1_ucm_relax_model                  4
% 51.43/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.43/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.43/7.00  --bmc1_ucm_layered_model                none
% 51.43/7.00  --bmc1_ucm_max_lemma_size               10
% 51.43/7.00  
% 51.43/7.00  ------ AIG Options
% 51.43/7.00  
% 51.43/7.00  --aig_mode                              false
% 51.43/7.00  
% 51.43/7.00  ------ Instantiation Options
% 51.43/7.00  
% 51.43/7.00  --instantiation_flag                    true
% 51.43/7.00  --inst_sos_flag                         true
% 51.43/7.00  --inst_sos_phase                        true
% 51.43/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.43/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.43/7.00  --inst_lit_sel_side                     num_symb
% 51.43/7.00  --inst_solver_per_active                1400
% 51.43/7.00  --inst_solver_calls_frac                1.
% 51.43/7.00  --inst_passive_queue_type               priority_queues
% 51.43/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.43/7.00  --inst_passive_queues_freq              [25;2]
% 51.43/7.00  --inst_dismatching                      true
% 51.43/7.00  --inst_eager_unprocessed_to_passive     true
% 51.43/7.00  --inst_prop_sim_given                   true
% 51.43/7.00  --inst_prop_sim_new                     false
% 51.43/7.00  --inst_subs_new                         false
% 51.43/7.00  --inst_eq_res_simp                      false
% 51.43/7.00  --inst_subs_given                       false
% 51.43/7.00  --inst_orphan_elimination               true
% 51.43/7.00  --inst_learning_loop_flag               true
% 51.43/7.00  --inst_learning_start                   3000
% 51.43/7.00  --inst_learning_factor                  2
% 51.43/7.00  --inst_start_prop_sim_after_learn       3
% 51.43/7.00  --inst_sel_renew                        solver
% 51.43/7.00  --inst_lit_activity_flag                true
% 51.43/7.00  --inst_restr_to_given                   false
% 51.43/7.00  --inst_activity_threshold               500
% 51.43/7.00  --inst_out_proof                        true
% 51.43/7.00  
% 51.43/7.00  ------ Resolution Options
% 51.43/7.00  
% 51.43/7.00  --resolution_flag                       true
% 51.43/7.00  --res_lit_sel                           adaptive
% 51.43/7.00  --res_lit_sel_side                      none
% 51.43/7.00  --res_ordering                          kbo
% 51.43/7.00  --res_to_prop_solver                    active
% 51.43/7.00  --res_prop_simpl_new                    false
% 51.43/7.00  --res_prop_simpl_given                  true
% 51.43/7.00  --res_passive_queue_type                priority_queues
% 51.43/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.43/7.00  --res_passive_queues_freq               [15;5]
% 51.43/7.00  --res_forward_subs                      full
% 51.43/7.00  --res_backward_subs                     full
% 51.43/7.00  --res_forward_subs_resolution           true
% 51.43/7.00  --res_backward_subs_resolution          true
% 51.43/7.00  --res_orphan_elimination                true
% 51.43/7.00  --res_time_limit                        2.
% 51.43/7.00  --res_out_proof                         true
% 51.43/7.00  
% 51.43/7.00  ------ Superposition Options
% 51.43/7.00  
% 51.43/7.00  --superposition_flag                    true
% 51.43/7.00  --sup_passive_queue_type                priority_queues
% 51.43/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.43/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.43/7.00  --demod_completeness_check              fast
% 51.43/7.00  --demod_use_ground                      true
% 51.43/7.00  --sup_to_prop_solver                    passive
% 51.43/7.00  --sup_prop_simpl_new                    true
% 51.43/7.00  --sup_prop_simpl_given                  true
% 51.43/7.00  --sup_fun_splitting                     true
% 51.43/7.00  --sup_smt_interval                      50000
% 51.43/7.00  
% 51.43/7.00  ------ Superposition Simplification Setup
% 51.43/7.00  
% 51.43/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.43/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.43/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.43/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.43/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.43/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.43/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.43/7.00  --sup_immed_triv                        [TrivRules]
% 51.43/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_immed_bw_main                     []
% 51.43/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.43/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.43/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_input_bw                          []
% 51.43/7.00  
% 51.43/7.00  ------ Combination Options
% 51.43/7.00  
% 51.43/7.00  --comb_res_mult                         3
% 51.43/7.00  --comb_sup_mult                         2
% 51.43/7.00  --comb_inst_mult                        10
% 51.43/7.00  
% 51.43/7.00  ------ Debug Options
% 51.43/7.00  
% 51.43/7.00  --dbg_backtrace                         false
% 51.43/7.00  --dbg_dump_prop_clauses                 false
% 51.43/7.00  --dbg_dump_prop_clauses_file            -
% 51.43/7.00  --dbg_out_stat                          false
% 51.43/7.00  ------ Parsing...
% 51.43/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.43/7.00  
% 51.43/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.43/7.00  
% 51.43/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.43/7.00  
% 51.43/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.43/7.00  ------ Proving...
% 51.43/7.00  ------ Problem Properties 
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  clauses                                 18
% 51.43/7.00  conjectures                             2
% 51.43/7.00  EPR                                     4
% 51.43/7.00  Horn                                    17
% 51.43/7.00  unary                                   13
% 51.43/7.00  binary                                  4
% 51.43/7.00  lits                                    24
% 51.43/7.00  lits eq                                 13
% 51.43/7.00  fd_pure                                 0
% 51.43/7.00  fd_pseudo                               0
% 51.43/7.00  fd_cond                                 0
% 51.43/7.00  fd_pseudo_cond                          2
% 51.43/7.00  AC symbols                              0
% 51.43/7.00  
% 51.43/7.00  ------ Schedule dynamic 5 is on 
% 51.43/7.00  
% 51.43/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  ------ 
% 51.43/7.00  Current options:
% 51.43/7.00  ------ 
% 51.43/7.00  
% 51.43/7.00  ------ Input Options
% 51.43/7.00  
% 51.43/7.00  --out_options                           all
% 51.43/7.00  --tptp_safe_out                         true
% 51.43/7.00  --problem_path                          ""
% 51.43/7.00  --include_path                          ""
% 51.43/7.00  --clausifier                            res/vclausify_rel
% 51.43/7.00  --clausifier_options                    ""
% 51.43/7.00  --stdin                                 false
% 51.43/7.00  --stats_out                             all
% 51.43/7.00  
% 51.43/7.00  ------ General Options
% 51.43/7.00  
% 51.43/7.00  --fof                                   false
% 51.43/7.00  --time_out_real                         305.
% 51.43/7.00  --time_out_virtual                      -1.
% 51.43/7.00  --symbol_type_check                     false
% 51.43/7.00  --clausify_out                          false
% 51.43/7.00  --sig_cnt_out                           false
% 51.43/7.00  --trig_cnt_out                          false
% 51.43/7.00  --trig_cnt_out_tolerance                1.
% 51.43/7.00  --trig_cnt_out_sk_spl                   false
% 51.43/7.00  --abstr_cl_out                          false
% 51.43/7.00  
% 51.43/7.00  ------ Global Options
% 51.43/7.00  
% 51.43/7.00  --schedule                              default
% 51.43/7.00  --add_important_lit                     false
% 51.43/7.00  --prop_solver_per_cl                    1000
% 51.43/7.00  --min_unsat_core                        false
% 51.43/7.00  --soft_assumptions                      false
% 51.43/7.00  --soft_lemma_size                       3
% 51.43/7.00  --prop_impl_unit_size                   0
% 51.43/7.00  --prop_impl_unit                        []
% 51.43/7.00  --share_sel_clauses                     true
% 51.43/7.00  --reset_solvers                         false
% 51.43/7.00  --bc_imp_inh                            [conj_cone]
% 51.43/7.00  --conj_cone_tolerance                   3.
% 51.43/7.00  --extra_neg_conj                        none
% 51.43/7.00  --large_theory_mode                     true
% 51.43/7.00  --prolific_symb_bound                   200
% 51.43/7.00  --lt_threshold                          2000
% 51.43/7.00  --clause_weak_htbl                      true
% 51.43/7.00  --gc_record_bc_elim                     false
% 51.43/7.00  
% 51.43/7.00  ------ Preprocessing Options
% 51.43/7.00  
% 51.43/7.00  --preprocessing_flag                    true
% 51.43/7.00  --time_out_prep_mult                    0.1
% 51.43/7.00  --splitting_mode                        input
% 51.43/7.00  --splitting_grd                         true
% 51.43/7.00  --splitting_cvd                         false
% 51.43/7.00  --splitting_cvd_svl                     false
% 51.43/7.00  --splitting_nvd                         32
% 51.43/7.00  --sub_typing                            true
% 51.43/7.00  --prep_gs_sim                           true
% 51.43/7.00  --prep_unflatten                        true
% 51.43/7.00  --prep_res_sim                          true
% 51.43/7.00  --prep_upred                            true
% 51.43/7.00  --prep_sem_filter                       exhaustive
% 51.43/7.00  --prep_sem_filter_out                   false
% 51.43/7.00  --pred_elim                             true
% 51.43/7.00  --res_sim_input                         true
% 51.43/7.00  --eq_ax_congr_red                       true
% 51.43/7.00  --pure_diseq_elim                       true
% 51.43/7.00  --brand_transform                       false
% 51.43/7.00  --non_eq_to_eq                          false
% 51.43/7.00  --prep_def_merge                        true
% 51.43/7.00  --prep_def_merge_prop_impl              false
% 51.43/7.00  --prep_def_merge_mbd                    true
% 51.43/7.00  --prep_def_merge_tr_red                 false
% 51.43/7.00  --prep_def_merge_tr_cl                  false
% 51.43/7.00  --smt_preprocessing                     true
% 51.43/7.00  --smt_ac_axioms                         fast
% 51.43/7.00  --preprocessed_out                      false
% 51.43/7.00  --preprocessed_stats                    false
% 51.43/7.00  
% 51.43/7.00  ------ Abstraction refinement Options
% 51.43/7.00  
% 51.43/7.00  --abstr_ref                             []
% 51.43/7.00  --abstr_ref_prep                        false
% 51.43/7.00  --abstr_ref_until_sat                   false
% 51.43/7.00  --abstr_ref_sig_restrict                funpre
% 51.43/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.43/7.00  --abstr_ref_under                       []
% 51.43/7.00  
% 51.43/7.00  ------ SAT Options
% 51.43/7.00  
% 51.43/7.00  --sat_mode                              false
% 51.43/7.00  --sat_fm_restart_options                ""
% 51.43/7.00  --sat_gr_def                            false
% 51.43/7.00  --sat_epr_types                         true
% 51.43/7.00  --sat_non_cyclic_types                  false
% 51.43/7.00  --sat_finite_models                     false
% 51.43/7.00  --sat_fm_lemmas                         false
% 51.43/7.00  --sat_fm_prep                           false
% 51.43/7.00  --sat_fm_uc_incr                        true
% 51.43/7.00  --sat_out_model                         small
% 51.43/7.00  --sat_out_clauses                       false
% 51.43/7.00  
% 51.43/7.00  ------ QBF Options
% 51.43/7.00  
% 51.43/7.00  --qbf_mode                              false
% 51.43/7.00  --qbf_elim_univ                         false
% 51.43/7.00  --qbf_dom_inst                          none
% 51.43/7.00  --qbf_dom_pre_inst                      false
% 51.43/7.00  --qbf_sk_in                             false
% 51.43/7.00  --qbf_pred_elim                         true
% 51.43/7.00  --qbf_split                             512
% 51.43/7.00  
% 51.43/7.00  ------ BMC1 Options
% 51.43/7.00  
% 51.43/7.00  --bmc1_incremental                      false
% 51.43/7.00  --bmc1_axioms                           reachable_all
% 51.43/7.00  --bmc1_min_bound                        0
% 51.43/7.00  --bmc1_max_bound                        -1
% 51.43/7.00  --bmc1_max_bound_default                -1
% 51.43/7.00  --bmc1_symbol_reachability              true
% 51.43/7.00  --bmc1_property_lemmas                  false
% 51.43/7.00  --bmc1_k_induction                      false
% 51.43/7.00  --bmc1_non_equiv_states                 false
% 51.43/7.00  --bmc1_deadlock                         false
% 51.43/7.00  --bmc1_ucm                              false
% 51.43/7.00  --bmc1_add_unsat_core                   none
% 51.43/7.00  --bmc1_unsat_core_children              false
% 51.43/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.43/7.00  --bmc1_out_stat                         full
% 51.43/7.00  --bmc1_ground_init                      false
% 51.43/7.00  --bmc1_pre_inst_next_state              false
% 51.43/7.00  --bmc1_pre_inst_state                   false
% 51.43/7.00  --bmc1_pre_inst_reach_state             false
% 51.43/7.00  --bmc1_out_unsat_core                   false
% 51.43/7.00  --bmc1_aig_witness_out                  false
% 51.43/7.00  --bmc1_verbose                          false
% 51.43/7.00  --bmc1_dump_clauses_tptp                false
% 51.43/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.43/7.00  --bmc1_dump_file                        -
% 51.43/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.43/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.43/7.00  --bmc1_ucm_extend_mode                  1
% 51.43/7.00  --bmc1_ucm_init_mode                    2
% 51.43/7.00  --bmc1_ucm_cone_mode                    none
% 51.43/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.43/7.00  --bmc1_ucm_relax_model                  4
% 51.43/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.43/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.43/7.00  --bmc1_ucm_layered_model                none
% 51.43/7.00  --bmc1_ucm_max_lemma_size               10
% 51.43/7.00  
% 51.43/7.00  ------ AIG Options
% 51.43/7.00  
% 51.43/7.00  --aig_mode                              false
% 51.43/7.00  
% 51.43/7.00  ------ Instantiation Options
% 51.43/7.00  
% 51.43/7.00  --instantiation_flag                    true
% 51.43/7.00  --inst_sos_flag                         true
% 51.43/7.00  --inst_sos_phase                        true
% 51.43/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.43/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.43/7.00  --inst_lit_sel_side                     none
% 51.43/7.00  --inst_solver_per_active                1400
% 51.43/7.00  --inst_solver_calls_frac                1.
% 51.43/7.00  --inst_passive_queue_type               priority_queues
% 51.43/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.43/7.00  --inst_passive_queues_freq              [25;2]
% 51.43/7.00  --inst_dismatching                      true
% 51.43/7.00  --inst_eager_unprocessed_to_passive     true
% 51.43/7.00  --inst_prop_sim_given                   true
% 51.43/7.00  --inst_prop_sim_new                     false
% 51.43/7.00  --inst_subs_new                         false
% 51.43/7.00  --inst_eq_res_simp                      false
% 51.43/7.00  --inst_subs_given                       false
% 51.43/7.00  --inst_orphan_elimination               true
% 51.43/7.00  --inst_learning_loop_flag               true
% 51.43/7.00  --inst_learning_start                   3000
% 51.43/7.00  --inst_learning_factor                  2
% 51.43/7.00  --inst_start_prop_sim_after_learn       3
% 51.43/7.00  --inst_sel_renew                        solver
% 51.43/7.00  --inst_lit_activity_flag                true
% 51.43/7.00  --inst_restr_to_given                   false
% 51.43/7.00  --inst_activity_threshold               500
% 51.43/7.00  --inst_out_proof                        true
% 51.43/7.00  
% 51.43/7.00  ------ Resolution Options
% 51.43/7.00  
% 51.43/7.00  --resolution_flag                       false
% 51.43/7.00  --res_lit_sel                           adaptive
% 51.43/7.00  --res_lit_sel_side                      none
% 51.43/7.00  --res_ordering                          kbo
% 51.43/7.00  --res_to_prop_solver                    active
% 51.43/7.00  --res_prop_simpl_new                    false
% 51.43/7.00  --res_prop_simpl_given                  true
% 51.43/7.00  --res_passive_queue_type                priority_queues
% 51.43/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.43/7.00  --res_passive_queues_freq               [15;5]
% 51.43/7.00  --res_forward_subs                      full
% 51.43/7.00  --res_backward_subs                     full
% 51.43/7.00  --res_forward_subs_resolution           true
% 51.43/7.00  --res_backward_subs_resolution          true
% 51.43/7.00  --res_orphan_elimination                true
% 51.43/7.00  --res_time_limit                        2.
% 51.43/7.00  --res_out_proof                         true
% 51.43/7.00  
% 51.43/7.00  ------ Superposition Options
% 51.43/7.00  
% 51.43/7.00  --superposition_flag                    true
% 51.43/7.00  --sup_passive_queue_type                priority_queues
% 51.43/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.43/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.43/7.00  --demod_completeness_check              fast
% 51.43/7.00  --demod_use_ground                      true
% 51.43/7.00  --sup_to_prop_solver                    passive
% 51.43/7.00  --sup_prop_simpl_new                    true
% 51.43/7.00  --sup_prop_simpl_given                  true
% 51.43/7.00  --sup_fun_splitting                     true
% 51.43/7.00  --sup_smt_interval                      50000
% 51.43/7.00  
% 51.43/7.00  ------ Superposition Simplification Setup
% 51.43/7.00  
% 51.43/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.43/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.43/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.43/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.43/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.43/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.43/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.43/7.00  --sup_immed_triv                        [TrivRules]
% 51.43/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_immed_bw_main                     []
% 51.43/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.43/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.43/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.43/7.00  --sup_input_bw                          []
% 51.43/7.00  
% 51.43/7.00  ------ Combination Options
% 51.43/7.00  
% 51.43/7.00  --comb_res_mult                         3
% 51.43/7.00  --comb_sup_mult                         2
% 51.43/7.00  --comb_inst_mult                        10
% 51.43/7.00  
% 51.43/7.00  ------ Debug Options
% 51.43/7.00  
% 51.43/7.00  --dbg_backtrace                         false
% 51.43/7.00  --dbg_dump_prop_clauses                 false
% 51.43/7.00  --dbg_dump_prop_clauses_file            -
% 51.43/7.00  --dbg_out_stat                          false
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  ------ Proving...
% 51.43/7.00  
% 51.43/7.00  
% 51.43/7.00  % SZS status Theorem for theBenchmark.p
% 51.43/7.00  
% 51.43/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.43/7.00  
% 51.43/7.00  fof(f15,conjecture,(
% 51.43/7.00    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f16,negated_conjecture,(
% 51.43/7.00    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 51.43/7.00    inference(negated_conjecture,[],[f15])).
% 51.43/7.00  
% 51.43/7.00  fof(f21,plain,(
% 51.43/7.00    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 51.43/7.00    inference(ennf_transformation,[],[f16])).
% 51.43/7.00  
% 51.43/7.00  fof(f22,plain,(
% 51.43/7.00    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 51.43/7.00    inference(flattening,[],[f21])).
% 51.43/7.00  
% 51.43/7.00  fof(f29,plain,(
% 51.43/7.00    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3))),
% 51.43/7.00    introduced(choice_axiom,[])).
% 51.43/7.00  
% 51.43/7.00  fof(f30,plain,(
% 51.43/7.00    sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 51.43/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29])).
% 51.43/7.00  
% 51.43/7.00  fof(f47,plain,(
% 51.43/7.00    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 51.43/7.00    inference(cnf_transformation,[],[f30])).
% 51.43/7.00  
% 51.43/7.00  fof(f6,axiom,(
% 51.43/7.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f38,plain,(
% 51.43/7.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 51.43/7.00    inference(cnf_transformation,[],[f6])).
% 51.43/7.00  
% 51.43/7.00  fof(f12,axiom,(
% 51.43/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f44,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.43/7.00    inference(cnf_transformation,[],[f12])).
% 51.43/7.00  
% 51.43/7.00  fof(f53,plain,(
% 51.43/7.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 51.43/7.00    inference(definition_unfolding,[],[f38,f44])).
% 51.43/7.00  
% 51.43/7.00  fof(f9,axiom,(
% 51.43/7.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f41,plain,(
% 51.43/7.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.43/7.00    inference(cnf_transformation,[],[f9])).
% 51.43/7.00  
% 51.43/7.00  fof(f10,axiom,(
% 51.43/7.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f42,plain,(
% 51.43/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 51.43/7.00    inference(cnf_transformation,[],[f10])).
% 51.43/7.00  
% 51.43/7.00  fof(f5,axiom,(
% 51.43/7.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f37,plain,(
% 51.43/7.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.43/7.00    inference(cnf_transformation,[],[f5])).
% 51.43/7.00  
% 51.43/7.00  fof(f13,axiom,(
% 51.43/7.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f45,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 51.43/7.00    inference(cnf_transformation,[],[f13])).
% 51.43/7.00  
% 51.43/7.00  fof(f54,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 51.43/7.00    inference(definition_unfolding,[],[f45,f44])).
% 51.43/7.00  
% 51.43/7.00  fof(f1,axiom,(
% 51.43/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f31,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.43/7.00    inference(cnf_transformation,[],[f1])).
% 51.43/7.00  
% 51.43/7.00  fof(f11,axiom,(
% 51.43/7.00    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f43,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 51.43/7.00    inference(cnf_transformation,[],[f11])).
% 51.43/7.00  
% 51.43/7.00  fof(f8,axiom,(
% 51.43/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f40,plain,(
% 51.43/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.43/7.00    inference(cnf_transformation,[],[f8])).
% 51.43/7.00  
% 51.43/7.00  fof(f2,axiom,(
% 51.43/7.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f23,plain,(
% 51.43/7.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 51.43/7.00    inference(nnf_transformation,[],[f2])).
% 51.43/7.00  
% 51.43/7.00  fof(f24,plain,(
% 51.43/7.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 51.43/7.00    inference(rectify,[],[f23])).
% 51.43/7.00  
% 51.43/7.00  fof(f25,plain,(
% 51.43/7.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 51.43/7.00    introduced(choice_axiom,[])).
% 51.43/7.00  
% 51.43/7.00  fof(f26,plain,(
% 51.43/7.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 51.43/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 51.43/7.00  
% 51.43/7.00  fof(f33,plain,(
% 51.43/7.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 51.43/7.00    inference(cnf_transformation,[],[f26])).
% 51.43/7.00  
% 51.43/7.00  fof(f4,axiom,(
% 51.43/7.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f17,plain,(
% 51.43/7.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 51.43/7.00    inference(rectify,[],[f4])).
% 51.43/7.00  
% 51.43/7.00  fof(f18,plain,(
% 51.43/7.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.43/7.00    inference(ennf_transformation,[],[f17])).
% 51.43/7.00  
% 51.43/7.00  fof(f27,plain,(
% 51.43/7.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 51.43/7.00    introduced(choice_axiom,[])).
% 51.43/7.00  
% 51.43/7.00  fof(f28,plain,(
% 51.43/7.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 51.43/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).
% 51.43/7.00  
% 51.43/7.00  fof(f36,plain,(
% 51.43/7.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 51.43/7.00    inference(cnf_transformation,[],[f28])).
% 51.43/7.00  
% 51.43/7.00  fof(f51,plain,(
% 51.43/7.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 51.43/7.00    inference(definition_unfolding,[],[f36,f44])).
% 51.43/7.00  
% 51.43/7.00  fof(f49,plain,(
% 51.43/7.00    r1_xboole_0(sK4,sK3)),
% 51.43/7.00    inference(cnf_transformation,[],[f30])).
% 51.43/7.00  
% 51.43/7.00  fof(f48,plain,(
% 51.43/7.00    r1_xboole_0(sK2,sK3)),
% 51.43/7.00    inference(cnf_transformation,[],[f30])).
% 51.43/7.00  
% 51.43/7.00  fof(f14,axiom,(
% 51.43/7.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f20,plain,(
% 51.43/7.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 51.43/7.00    inference(ennf_transformation,[],[f14])).
% 51.43/7.00  
% 51.43/7.00  fof(f46,plain,(
% 51.43/7.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 51.43/7.00    inference(cnf_transformation,[],[f20])).
% 51.43/7.00  
% 51.43/7.00  fof(f3,axiom,(
% 51.43/7.00    v1_xboole_0(k1_xboole_0)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f34,plain,(
% 51.43/7.00    v1_xboole_0(k1_xboole_0)),
% 51.43/7.00    inference(cnf_transformation,[],[f3])).
% 51.43/7.00  
% 51.43/7.00  fof(f7,axiom,(
% 51.43/7.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 51.43/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.43/7.00  
% 51.43/7.00  fof(f19,plain,(
% 51.43/7.00    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 51.43/7.01    inference(ennf_transformation,[],[f7])).
% 51.43/7.01  
% 51.43/7.01  fof(f39,plain,(
% 51.43/7.01    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 51.43/7.01    inference(cnf_transformation,[],[f19])).
% 51.43/7.01  
% 51.43/7.01  fof(f50,plain,(
% 51.43/7.01    sK2 != sK4),
% 51.43/7.01    inference(cnf_transformation,[],[f30])).
% 51.43/7.01  
% 51.43/7.01  cnf(c_18,negated_conjecture,
% 51.43/7.01      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(cnf_transformation,[],[f47]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f53]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_10,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f41]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_342,plain,
% 51.43/7.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_7,c_10]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_11,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 51.43/7.01      inference(cnf_transformation,[],[f42]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1281,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_342,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f37]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1294,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1281,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2348,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_18,c_1294]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2376,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_2348,c_1294]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_13,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f54]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2518,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) = sK4 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_13]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_0,plain,
% 51.43/7.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(cnf_transformation,[],[f31]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_729,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1179,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_13,c_729]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1415,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1179,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1416,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1415,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6841,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),sK2) = k4_xboole_0(sK4,sK2) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2518,c_1416]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_9,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(cnf_transformation,[],[f40]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7928,plain,
% 51.43/7.01      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK2,k4_xboole_0(sK4,sK2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6841,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7934,plain,
% 51.43/7.01      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK2,sK4) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_7928,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1178,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_9,c_729]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2149,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_1178]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4195,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2149,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4199,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_4195,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_219579,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_7934,c_4199]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_883,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2860,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_883,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2522,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(sK2,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3863,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,sK2),sK3) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2522,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6378,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),sK3) = k4_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2860,c_3863]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6414,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),sK3) = k4_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_6378,c_2376]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1285,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6464,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),sK3),k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6414,c_1285]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7715,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6464,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3862,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2522,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3970,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK2),sK3) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_3862,c_3863]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7723,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = k4_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_7715,c_6,c_3970]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1187,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_729,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1191,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1187,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2319,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_18,c_1191]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2337,plain,
% 51.43/7.01      ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_2319,c_1191]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6834,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(k4_xboole_0(X0,X2),X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_1416]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_56193,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),sK3) = k4_xboole_0(k4_xboole_0(sK4,X0),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2337,c_6834]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_56427,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK2,X0),sK3) = k4_xboole_0(k4_xboole_0(sK4,X0),sK3) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_56193,c_6834]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_60779,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k4_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(light_normalisation,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_7723,c_7723,c_56427]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_219631,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))),k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_60779,c_4199]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2838,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = sK4 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_883]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1282,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_729,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1293,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1282,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_10676,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1293,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_10700,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_10676,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_78773,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_9,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2172,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1178,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2181,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_2172,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_78803,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2181,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_78914,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2860,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_739,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_12,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_743,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_739,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2099,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_743]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79621,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_78914,c_2099]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79815,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_78803,c_79621]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1275,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_342,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_677,plain,
% 51.43/7.01      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1300,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1275,c_677]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6889,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1416,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6907,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_6889,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_18620,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1300,c_6907]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79017,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_10700,c_743]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79033,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_10700,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79111,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_79017,c_79033]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2314,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_1191]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79112,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_79111,c_2314]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79816,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X1,X0))) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_79815,c_18620,c_79112]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79861,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_78773,c_79816]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79862,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_79861,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83048,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2838,c_79862]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_219661,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK4,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_83048,c_4199]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1,plain,
% 51.43/7.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 51.43/7.01      inference(cnf_transformation,[],[f33]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_341,plain,
% 51.43/7.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 51.43/7.01      | v1_xboole_0(X0) = iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4,plain,
% 51.43/7.01      ( ~ r1_xboole_0(X0,X1)
% 51.43/7.01      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.43/7.01      inference(cnf_transformation,[],[f51]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_16,negated_conjecture,
% 51.43/7.01      ( r1_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(cnf_transformation,[],[f49]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_123,plain,
% 51.43/7.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 51.43/7.01      | sK3 != X2
% 51.43/7.01      | sK4 != X1 ),
% 51.43/7.01      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_124,plain,
% 51.43/7.01      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 51.43/7.01      inference(unflattening,[status(thm)],[c_123]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_336,plain,
% 51.43/7.01      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2510,plain,
% 51.43/7.01      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_2376,c_336]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6817,plain,
% 51.43/7.01      ( v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_341,c_2510]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_17,negated_conjecture,
% 51.43/7.01      ( r1_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(cnf_transformation,[],[f48]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_132,plain,
% 51.43/7.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 51.43/7.01      | sK3 != X2
% 51.43/7.01      | sK2 != X1 ),
% 51.43/7.01      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_133,plain,
% 51.43/7.01      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 51.43/7.01      inference(unflattening,[status(thm)],[c_132]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_335,plain,
% 51.43/7.01      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6814,plain,
% 51.43/7.01      ( v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = iProver_top ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_341,c_335]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_14,plain,
% 51.43/7.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 51.43/7.01      inference(cnf_transformation,[],[f46]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_338,plain,
% 51.43/7.01      ( X0 = X1
% 51.43/7.01      | v1_xboole_0(X1) != iProver_top
% 51.43/7.01      | v1_xboole_0(X0) != iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_202995,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0
% 51.43/7.01      | v1_xboole_0(X0) != iProver_top ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6814,c_338]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_203324,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6817,c_202995]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3,plain,
% 51.43/7.01      ( v1_xboole_0(k1_xboole_0) ),
% 51.43/7.01      inference(cnf_transformation,[],[f34]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_339,plain,
% 51.43/7.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_203322,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_339,c_202995]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_203621,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_203324,c_203322]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220008,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))),k2_xboole_0(sK4,X1)) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_219661,c_203621]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_989,plain,
% 51.43/7.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_677,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2327,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1191,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1413,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1179,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1419,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_1413,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_732,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_18,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1277,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_732,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1298,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1277,c_677]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1566,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1419,c_1298]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1581,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_1566,c_732]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1659,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK4,X1)),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1581,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1660,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK4,X1)),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1659,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_17220,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),k2_xboole_0(sK2,sK3)) = k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2860,c_1660]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_17289,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_17220,c_1581]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1283,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK2,sK3)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_732,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1292,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1283,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1536,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,sK4) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1292,c_1419]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1988,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(X0,sK4) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_1536]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42148,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_17289,c_1988]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1571,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1298,c_13]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_41894,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),k1_xboole_0),k1_xboole_0) = k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_17289,c_1571]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_5026,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1285,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2103,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_743]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1288,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2132,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,X2)) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_2103,c_1288]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_5036,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_5026,c_2132]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3084,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2099,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_5274,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_3084,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2117,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_743,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4255,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2314,c_2117]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4277,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_4255,c_2314]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_5288,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_5274,c_4277]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7952,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_10,c_1288]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8126,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_7952,c_10]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_18607,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2860,c_6907]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_18801,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = X0 ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_18607,c_1419]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42004,plain,
% 51.43/7.01      ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK4,X0),X1)) = sK4 ),
% 51.43/7.01      inference(demodulation,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_41894,c_5036,c_5288,c_8126,c_18801]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42250,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) = k2_xboole_0(sK4,k1_xboole_0) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_42148,c_42004]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42251,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK4) = sK4 ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_42250,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2517,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(X0,sK3)) = k4_xboole_0(k2_xboole_0(sK4,X0),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3838,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(sK4,X0),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2517,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_6173,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK2,X0),sK3) = k4_xboole_0(k2_xboole_0(X0,sK4),sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_3838]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42662,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),sK3) = k4_xboole_0(sK4,sK3) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_42251,c_6173]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_42681,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK4,X0),X1)),sK3) = k4_xboole_0(sK2,sK3) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_42662,c_2376]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1280,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1295,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1280,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12788,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2327,c_1295]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12975,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_12788,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_13281,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X0),X1),X3)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_12975]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_103696,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,X0),X1),sK3),k2_xboole_0(k4_xboole_0(sK2,sK3),X2)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_42681,c_13281]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_134132,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(k4_xboole_0(sK2,sK3),X1)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_103696]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_134344,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2327,c_134132]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4362,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_9,c_2327]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4410,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_4362,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_11341,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_4410]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151796,plain,
% 51.43/7.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3)))) = k2_xboole_0(k2_xboole_0(X1,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_134344,c_11341]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151821,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_134344,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83226,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_79862,c_2327]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83347,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_83226,c_79862]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8265,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_8126,c_1288]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8274,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_8265,c_8126]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8275,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_8274,c_10]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83231,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X3,X2),X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_79862,c_8275]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83345,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_83231,c_79862]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83348,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X2)))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_83347,c_83345]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4264,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2314,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8266,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_8126,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8272,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_8266,c_8126]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8273,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_8272,c_10]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_20786,plain,
% 51.43/7.01      ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_8273,c_2327]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_83349,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_83348,c_4264,c_20786]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151849,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)) = k2_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_151821,c_5288,c_83349]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2352,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1294,c_1419]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_138656,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_2352]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151817,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X1),sK3),k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_134344,c_138656]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151853,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK3),X1),k1_xboole_0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_151817,c_151849]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1276,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_729,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1299,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_1276,c_677]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_14834,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1299,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_14866,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_14834,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12867,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1295,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12892,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_12867,c_9]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79074,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_10700,c_8273]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_10615,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_1293]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8348,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_2181]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_73147,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_10615,c_8348]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_24336,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1293,c_8348]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_24562,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X0,X1)) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_24336,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_24563,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_24562,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_73340,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 51.43/7.01      inference(light_normalisation,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_73147,c_14866,c_24563]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79431,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_79074,c_73340,c_79112]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_97338,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 51.43/7.01      inference(light_normalisation,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_12892,c_79431,c_83349]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_97690,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_97338,c_0]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_110529,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 51.43/7.01      inference(light_normalisation,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_14866,c_83349,c_97690]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_110716,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X3,X2))) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_11,c_110529]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_78905,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1288,c_10700]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_79626,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X1,X3),X2)) = k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X3),X2)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_78905,c_1288,c_79112]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_111267,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,X3),X1)) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_110716,c_79626]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151854,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK3),X0),sK3),k2_xboole_0(X1,k4_xboole_0(sK2,sK3))) = k2_xboole_0(X1,k4_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_151853,c_5288,c_111267]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_151866,plain,
% 51.43/7.01      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_151796,c_151849,c_151854]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220009,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK3),X1)) = k4_xboole_0(X0,k2_xboole_0(sK4,X1)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_220008,c_6,c_989,c_151866]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220046,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,X1),sK3))),k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X1),sK3))) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_219631,c_220009]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_56634,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_56427,c_17289]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1567,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(sK4,X0),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_1298,c_1419]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_9176,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,X0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_0,c_1567]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_64237,plain,
% 51.43/7.01      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK4),k1_xboole_0) = k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_56634,c_9176]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_56631,plain,
% 51.43/7.01      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),sK3),sK4) = sK4 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_56427,c_42251]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_64343,plain,
% 51.43/7.01      ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
% 51.43/7.01      inference(light_normalisation,[status(thm)],[c_64237,c_56631]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_64344,plain,
% 51.43/7.01      ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK2,X0),sK3)) = sK4 ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_64343,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220047,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,sK4) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_220046,c_1416,c_64344]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220108,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK4,sK4))),k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK4,sK4))) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_219579,c_220047]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12781,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2860,c_1295]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_12982,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_12781,c_12]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_15265,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X3)),k1_xboole_0) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_12982,c_11]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_15286,plain,
% 51.43/7.01      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_15265,c_6]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_220109,plain,
% 51.43/7.01      ( k4_xboole_0(X0,k2_xboole_0(sK2,sK4)) = k4_xboole_0(X0,sK2) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_220108,c_6,c_342,c_15286]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2152,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_9,c_1178]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_221083,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK2),sK2),sK2) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_220109,c_2152]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_16579,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_9,c_1300]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_16683,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_16579,c_1300]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_221334,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
% 51.43/7.01      inference(demodulation,[status(thm)],[c_221083,c_16683]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_202996,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = X0
% 51.43/7.01      | v1_xboole_0(X0) != iProver_top ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_6817,c_338]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_203002,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0
% 51.43/7.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_202996]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_206,plain,
% 51.43/7.01      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 51.43/7.01      theory(equality) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_704,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(X0,X1)
% 51.43/7.01      | k4_xboole_0(sK2,sK3) != X1
% 51.43/7.01      | sK2 != X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_206]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_46709,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK4)
% 51.43/7.01      | k4_xboole_0(sK2,sK3) != sK4
% 51.43/7.01      | sK2 != sK2 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_704]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_202,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_840,plain,
% 51.43/7.01      ( X0 != X1
% 51.43/7.01      | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 51.43/7.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_202]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_9693,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) != X0
% 51.43/7.01      | k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 51.43/7.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_840]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_9694,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 51.43/7.01      | k4_xboole_0(sK4,sK2) != k1_xboole_0
% 51.43/7.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_9693]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_383,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) != X0
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != X0
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_202]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_480,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) != k4_xboole_0(X0,X1)
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_383]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_7593,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,sK2) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK4,sK2)
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_480]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_201,plain,( X0 = X0 ),theory(equality) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_4095,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) = k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_201]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_3816,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_201]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_661,plain,
% 51.43/7.01      ( X0 != X1
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != X1
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_202]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1461,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != X0
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_661]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2676,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k4_xboole_0(sK2,sK4)
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 51.43/7.01      | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,sK4) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_1461]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2516,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k1_xboole_0 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2376,c_1179]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_8,plain,
% 51.43/7.01      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 51.43/7.01      inference(cnf_transformation,[],[f39]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_2586,plain,
% 51.43/7.01      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) != k1_xboole_0
% 51.43/7.01      | k4_xboole_0(sK2,sK3) = sK4 ),
% 51.43/7.01      inference(superposition,[status(thm)],[c_2516,c_8]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_653,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK2,sK4),X0) != k4_xboole_0(X0,k4_xboole_0(sK2,sK4))
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_8]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1974,plain,
% 51.43/7.01      ( k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4)) != k4_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK2,sK4))
% 51.43/7.01      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK4) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_653]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_483,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2) | sK2 = X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_8]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1938,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2) | sK2 = sK2 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_483]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_1203,plain,
% 51.43/7.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_133]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_502,plain,
% 51.43/7.01      ( r2_hidden(sK0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 51.43/7.01      | v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_1]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_423,plain,
% 51.43/7.01      ( ~ v1_xboole_0(X0)
% 51.43/7.01      | ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 51.43/7.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = X0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_14]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_425,plain,
% 51.43/7.01      ( ~ v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 51.43/7.01      | ~ v1_xboole_0(k1_xboole_0)
% 51.43/7.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_423]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_352,plain,
% 51.43/7.01      ( k4_xboole_0(sK2,sK4) != k4_xboole_0(sK4,sK2) | sK2 = sK4 ),
% 51.43/7.01      inference(instantiation,[status(thm)],[c_8]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_38,plain,
% 51.43/7.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 51.43/7.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(c_15,negated_conjecture,
% 51.43/7.01      ( sK2 != sK4 ),
% 51.43/7.01      inference(cnf_transformation,[],[f50]) ).
% 51.43/7.01  
% 51.43/7.01  cnf(contradiction,plain,
% 51.43/7.01      ( $false ),
% 51.43/7.01      inference(minisat,
% 51.43/7.01                [status(thm)],
% 51.43/7.01                [c_221334,c_203002,c_46709,c_9694,c_7593,c_4095,c_3816,
% 51.43/7.01                 c_2676,c_2586,c_1974,c_1938,c_1203,c_502,c_425,c_352,
% 51.43/7.01                 c_38,c_3,c_15]) ).
% 51.43/7.01  
% 51.43/7.01  
% 51.43/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.43/7.01  
% 51.43/7.01  ------                               Statistics
% 51.43/7.01  
% 51.43/7.01  ------ General
% 51.43/7.01  
% 51.43/7.01  abstr_ref_over_cycles:                  0
% 51.43/7.01  abstr_ref_under_cycles:                 0
% 51.43/7.01  gc_basic_clause_elim:                   0
% 51.43/7.01  forced_gc_time:                         0
% 51.43/7.01  parsing_time:                           0.01
% 51.43/7.01  unif_index_cands_time:                  0.
% 51.43/7.01  unif_index_add_time:                    0.
% 51.43/7.01  orderings_time:                         0.
% 51.43/7.01  out_proof_time:                         0.017
% 51.43/7.01  total_time:                             6.434
% 51.43/7.01  num_of_symbols:                         42
% 51.43/7.01  num_of_terms:                           313693
% 51.43/7.01  
% 51.43/7.01  ------ Preprocessing
% 51.43/7.01  
% 51.43/7.01  num_of_splits:                          0
% 51.43/7.01  num_of_split_atoms:                     0
% 51.43/7.01  num_of_reused_defs:                     0
% 51.43/7.01  num_eq_ax_congr_red:                    9
% 51.43/7.01  num_of_sem_filtered_clauses:            1
% 51.43/7.01  num_of_subtypes:                        0
% 51.43/7.01  monotx_restored_types:                  0
% 51.43/7.01  sat_num_of_epr_types:                   0
% 51.43/7.01  sat_num_of_non_cyclic_types:            0
% 51.43/7.01  sat_guarded_non_collapsed_types:        0
% 51.43/7.01  num_pure_diseq_elim:                    0
% 51.43/7.01  simp_replaced_by:                       0
% 51.43/7.01  res_preprocessed:                       86
% 51.43/7.01  prep_upred:                             0
% 51.43/7.01  prep_unflattend:                        4
% 51.43/7.01  smt_new_axioms:                         0
% 51.43/7.01  pred_elim_cands:                        2
% 51.43/7.01  pred_elim:                              1
% 51.43/7.01  pred_elim_cl:                           1
% 51.43/7.01  pred_elim_cycles:                       3
% 51.43/7.01  merged_defs:                            0
% 51.43/7.01  merged_defs_ncl:                        0
% 51.43/7.01  bin_hyper_res:                          0
% 51.43/7.01  prep_cycles:                            4
% 51.43/7.01  pred_elim_time:                         0.001
% 51.43/7.01  splitting_time:                         0.
% 51.43/7.01  sem_filter_time:                        0.
% 51.43/7.01  monotx_time:                            0.
% 51.43/7.01  subtype_inf_time:                       0.
% 51.43/7.01  
% 51.43/7.01  ------ Problem properties
% 51.43/7.01  
% 51.43/7.01  clauses:                                18
% 51.43/7.01  conjectures:                            2
% 51.43/7.01  epr:                                    4
% 51.43/7.01  horn:                                   17
% 51.43/7.01  ground:                                 3
% 51.43/7.01  unary:                                  13
% 51.43/7.01  binary:                                 4
% 51.43/7.01  lits:                                   24
% 51.43/7.01  lits_eq:                                13
% 51.43/7.01  fd_pure:                                0
% 51.43/7.01  fd_pseudo:                              0
% 51.43/7.01  fd_cond:                                0
% 51.43/7.01  fd_pseudo_cond:                         2
% 51.43/7.01  ac_symbols:                             0
% 51.43/7.01  
% 51.43/7.01  ------ Propositional Solver
% 51.43/7.01  
% 51.43/7.01  prop_solver_calls:                      47
% 51.43/7.01  prop_fast_solver_calls:                 1102
% 51.43/7.01  smt_solver_calls:                       0
% 51.43/7.01  smt_fast_solver_calls:                  0
% 51.43/7.01  prop_num_of_clauses:                    44498
% 51.43/7.01  prop_preprocess_simplified:             34813
% 51.43/7.01  prop_fo_subsumed:                       0
% 51.43/7.01  prop_solver_time:                       0.
% 51.43/7.01  smt_solver_time:                        0.
% 51.43/7.01  smt_fast_solver_time:                   0.
% 51.43/7.01  prop_fast_solver_time:                  0.
% 51.43/7.01  prop_unsat_core_time:                   0.003
% 51.43/7.01  
% 51.43/7.01  ------ QBF
% 51.43/7.01  
% 51.43/7.01  qbf_q_res:                              0
% 51.43/7.01  qbf_num_tautologies:                    0
% 51.43/7.01  qbf_prep_cycles:                        0
% 51.43/7.01  
% 51.43/7.01  ------ BMC1
% 51.43/7.01  
% 51.43/7.01  bmc1_current_bound:                     -1
% 51.43/7.01  bmc1_last_solved_bound:                 -1
% 51.43/7.01  bmc1_unsat_core_size:                   -1
% 51.43/7.01  bmc1_unsat_core_parents_size:           -1
% 51.43/7.01  bmc1_merge_next_fun:                    0
% 51.43/7.01  bmc1_unsat_core_clauses_time:           0.
% 51.43/7.01  
% 51.43/7.01  ------ Instantiation
% 51.43/7.01  
% 51.43/7.01  inst_num_of_clauses:                    1646
% 51.43/7.01  inst_num_in_passive:                    358
% 51.43/7.01  inst_num_in_active:                     2794
% 51.43/7.01  inst_num_in_unprocessed:                679
% 51.43/7.01  inst_num_of_loops:                      3619
% 51.43/7.01  inst_num_of_learning_restarts:          1
% 51.43/7.01  inst_num_moves_active_passive:          824
% 51.43/7.01  inst_lit_activity:                      0
% 51.43/7.01  inst_lit_activity_moves:                0
% 51.43/7.01  inst_num_tautologies:                   0
% 51.43/7.01  inst_num_prop_implied:                  0
% 51.43/7.01  inst_num_existing_simplified:           0
% 51.43/7.01  inst_num_eq_res_simplified:             0
% 51.43/7.01  inst_num_child_elim:                    0
% 51.43/7.01  inst_num_of_dismatching_blockings:      9777
% 51.43/7.01  inst_num_of_non_proper_insts:           12804
% 51.43/7.01  inst_num_of_duplicates:                 0
% 51.43/7.01  inst_inst_num_from_inst_to_res:         0
% 51.43/7.01  inst_dismatching_checking_time:         0.
% 51.43/7.01  
% 51.43/7.01  ------ Resolution
% 51.43/7.01  
% 51.43/7.01  res_num_of_clauses:                     24
% 51.43/7.01  res_num_in_passive:                     24
% 51.43/7.01  res_num_in_active:                      0
% 51.43/7.01  res_num_of_loops:                       90
% 51.43/7.01  res_forward_subset_subsumed:            1144
% 51.43/7.01  res_backward_subset_subsumed:           8
% 51.43/7.01  res_forward_subsumed:                   0
% 51.43/7.01  res_backward_subsumed:                  0
% 51.43/7.01  res_forward_subsumption_resolution:     0
% 51.43/7.01  res_backward_subsumption_resolution:    0
% 51.43/7.01  res_clause_to_clause_subsumption:       313650
% 51.43/7.01  res_orphan_elimination:                 0
% 51.43/7.01  res_tautology_del:                      795
% 51.43/7.01  res_num_eq_res_simplified:              0
% 51.43/7.01  res_num_sel_changes:                    0
% 51.43/7.01  res_moves_from_active_to_pass:          0
% 51.43/7.01  
% 51.43/7.01  ------ Superposition
% 51.43/7.01  
% 51.43/7.01  sup_time_total:                         0.
% 51.43/7.01  sup_time_generating:                    0.
% 51.43/7.01  sup_time_sim_full:                      0.
% 51.43/7.01  sup_time_sim_immed:                     0.
% 51.43/7.01  
% 51.43/7.01  sup_num_of_clauses:                     14710
% 51.43/7.01  sup_num_in_active:                      619
% 51.43/7.01  sup_num_in_passive:                     14091
% 51.43/7.01  sup_num_of_loops:                       722
% 51.43/7.01  sup_fw_superposition:                   46946
% 51.43/7.01  sup_bw_superposition:                   43312
% 51.43/7.01  sup_immediate_simplified:               60934
% 51.43/7.01  sup_given_eliminated:                   15
% 51.43/7.01  comparisons_done:                       0
% 51.43/7.01  comparisons_avoided:                    0
% 51.43/7.01  
% 51.43/7.01  ------ Simplifications
% 51.43/7.01  
% 51.43/7.01  
% 51.43/7.01  sim_fw_subset_subsumed:                 18
% 51.43/7.01  sim_bw_subset_subsumed:                 0
% 51.43/7.01  sim_fw_subsumed:                        9429
% 51.43/7.01  sim_bw_subsumed:                        242
% 51.43/7.01  sim_fw_subsumption_res:                 0
% 51.43/7.01  sim_bw_subsumption_res:                 0
% 51.43/7.01  sim_tautology_del:                      324
% 51.43/7.01  sim_eq_tautology_del:                   17687
% 51.43/7.01  sim_eq_res_simp:                        13
% 51.43/7.01  sim_fw_demodulated:                     41033
% 51.43/7.01  sim_bw_demodulated:                     674
% 51.43/7.01  sim_light_normalised:                   23781
% 51.43/7.01  sim_joinable_taut:                      0
% 51.43/7.01  sim_joinable_simp:                      0
% 51.43/7.01  sim_ac_normalised:                      0
% 51.43/7.01  sim_smt_subsumption:                    0
% 51.43/7.01  
%------------------------------------------------------------------------------
