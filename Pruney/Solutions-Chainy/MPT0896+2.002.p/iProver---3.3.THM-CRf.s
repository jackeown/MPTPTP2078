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
% DateTime   : Thu Dec  3 11:58:39 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 995 expanded)
%              Number of clauses        :   52 ( 185 expanded)
%              Number of leaves         :    8 ( 257 expanded)
%              Depth                    :   24
%              Number of atoms          :  343 (5369 expanded)
%              Number of equality atoms :  342 (5368 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f30])).

fof(f57,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f74,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f57,f51,f51])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f48,f44,f44,f44])).

fof(f58,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f49,f44,f44,f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f47,f44,f44])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f50,f44,f44,f44])).

fof(f62,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_28,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1216,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK4,sK5) = X0 ),
    inference(superposition,[status(thm)],[c_28,c_17])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1221,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK4,sK5) = X0 ),
    inference(superposition,[status(thm)],[c_28,c_17])).

cnf(c_1245,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | k2_zfmisc_1(sK4,sK5) = X0 ),
    inference(demodulation,[status(thm)],[c_1221,c_28])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_522,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1308,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1468,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2948,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_2977,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK4,sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1216,c_27,c_26,c_25,c_24,c_1245,c_2948])).

cnf(c_2987,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
    inference(equality_resolution,[status(thm)],[c_2977])).

cnf(c_7198,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),X1) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2987,c_22])).

cnf(c_16,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1058,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK6 = X1 ),
    inference(superposition,[status(thm)],[c_28,c_16])).

cnf(c_1631,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK6 = sK2 ),
    inference(equality_resolution,[status(thm)],[c_1058])).

cnf(c_12,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2256,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK7 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_28,c_12])).

cnf(c_15,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1005,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK7 = X2 ),
    inference(superposition,[status(thm)],[c_28,c_15])).

cnf(c_1028,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK7 = X2 ),
    inference(demodulation,[status(thm)],[c_1005,c_28])).

cnf(c_3323,plain,
    ( sK7 = X2
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_27,c_26,c_25,c_24,c_1028,c_2948])).

cnf(c_3324,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK7 = X2 ),
    inference(renaming,[status(thm)],[c_3323])).

cnf(c_3333,plain,
    ( sK7 = sK3 ),
    inference(equality_resolution,[status(thm)],[c_3324])).

cnf(c_23,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6589,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_3333,c_23])).

cnf(c_6593,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_6589])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2255,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2 ),
    inference(superposition,[status(thm)],[c_4,c_12])).

cnf(c_7194,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2987,c_2255])).

cnf(c_7203,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | sK4 = X0 ),
    inference(superposition,[status(thm)],[c_2987,c_17])).

cnf(c_8177,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0
    | sK4 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_7203])).

cnf(c_7208,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | sK5 = X1 ),
    inference(superposition,[status(thm)],[c_2987,c_16])).

cnf(c_8354,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0
    | sK5 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_7208])).

cnf(c_9349,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7198,c_27,c_26,c_25,c_24,c_1631,c_2948,c_6593,c_7194,c_8177,c_8354])).

cnf(c_9350,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_9349])).

cnf(c_9595,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK5) = k2_zfmisc_1(sK0,sK1)
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_9350,c_2987])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9613,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_9595,c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_467,plain,
    ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_592,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_9625,plain,
    ( sK5 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9613,c_27,c_26,c_592])).

cnf(c_9869,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_9625,c_2987])).

cnf(c_9879,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_9869,c_4])).

cnf(c_9976,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9879,c_27,c_26,c_592])).

cnf(c_10020,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9976,c_26])).

cnf(c_10022,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10020])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:44:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.41/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.99  
% 3.41/0.99  ------  iProver source info
% 3.41/0.99  
% 3.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.99  git: non_committed_changes: false
% 3.41/0.99  git: last_make_outside_of_git: false
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     num_symb
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       true
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 28
% 3.41/0.99  conjectures                             6
% 3.41/0.99  EPR                                     8
% 3.41/0.99  Horn                                    18
% 3.41/0.99  unary                                   13
% 3.41/0.99  binary                                  2
% 3.41/0.99  lits                                    65
% 3.41/0.99  lits eq                                 50
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 4
% 3.41/0.99  fd_pseudo_cond                          7
% 3.41/0.99  AC symbols                              0
% 3.41/0.99  
% 3.41/0.99  ------ Schedule dynamic 5 is on 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     none
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       false
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status Theorem for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99   Resolution empty clause
% 3.41/0.99  
% 3.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f12,conjecture,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f13,negated_conjecture,(
% 3.41/0.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/0.99    inference(negated_conjecture,[],[f12])).
% 3.41/0.99  
% 3.41/0.99  fof(f22,plain,(
% 3.41/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.41/0.99    inference(ennf_transformation,[],[f13])).
% 3.41/0.99  
% 3.41/0.99  fof(f23,plain,(
% 3.41/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.41/0.99    inference(flattening,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f30,plain,(
% 3.41/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f31,plain,(
% 3.41/0.99    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f30])).
% 3.41/0.99  
% 3.41/0.99  fof(f57,plain,(
% 3.41/0.99    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f10,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f51,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f74,plain,(
% 3.41/0.99    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 3.41/0.99    inference(definition_unfolding,[],[f57,f51,f51])).
% 3.41/0.99  
% 3.41/0.99  fof(f9,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f20,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.41/0.99    inference(ennf_transformation,[],[f9])).
% 3.41/0.99  
% 3.41/0.99  fof(f21,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.41/0.99    inference(flattening,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  fof(f48,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f7,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f44,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f68,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f48,f44,f44,f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f58,plain,(
% 3.41/0.99    k1_xboole_0 != sK0),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f59,plain,(
% 3.41/0.99    k1_xboole_0 != sK1),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f60,plain,(
% 3.41/0.99    k1_xboole_0 != sK2),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f61,plain,(
% 3.41/0.99    k1_xboole_0 != sK3),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f28,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.41/0.99    inference(nnf_transformation,[],[f11])).
% 3.41/0.99  
% 3.41/0.99  fof(f29,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/0.99    inference(flattening,[],[f28])).
% 3.41/0.99  
% 3.41/0.99  fof(f52,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f29])).
% 3.41/0.99  
% 3.41/0.99  fof(f73,plain,(
% 3.41/0.99    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.41/0.99    inference(definition_unfolding,[],[f52,f51])).
% 3.41/0.99  
% 3.41/0.99  fof(f49,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f67,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f49,f44,f44,f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f8,axiom,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f18,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.41/0.99    inference(ennf_transformation,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f19,plain,(
% 3.41/0.99    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.41/0.99    inference(flattening,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f47,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f19])).
% 3.41/0.99  
% 3.41/0.99  fof(f63,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f47,f44,f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f50,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f66,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f50,f44,f44,f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f62,plain,(
% 3.41/0.99    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 3.41/0.99    inference(cnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f3,axiom,(
% 3.41/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f26,plain,(
% 3.41/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.41/0.99    inference(nnf_transformation,[],[f3])).
% 3.41/0.99  
% 3.41/0.99  fof(f27,plain,(
% 3.41/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.41/0.99    inference(flattening,[],[f26])).
% 3.41/0.99  
% 3.41/0.99  fof(f38,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.41/0.99    inference(cnf_transformation,[],[f27])).
% 3.41/0.99  
% 3.41/0.99  fof(f77,plain,(
% 3.41/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.41/0.99    inference(equality_resolution,[],[f38])).
% 3.41/0.99  
% 3.41/0.99  fof(f37,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.41/0.99    inference(cnf_transformation,[],[f27])).
% 3.41/0.99  
% 3.41/0.99  fof(f78,plain,(
% 3.41/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.41/0.99    inference(equality_resolution,[],[f37])).
% 3.41/0.99  
% 3.41/0.99  fof(f36,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f27])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_28,negated_conjecture,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
% 3.41/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_17,plain,
% 3.41/0.99      ( X0 = X1
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1216,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | k2_zfmisc_1(sK4,sK5) = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_28,c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_27,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_26,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_25,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK2 ),
% 3.41/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_24,negated_conjecture,
% 3.41/0.99      ( k1_xboole_0 != sK3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1221,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | k2_zfmisc_1(sK4,sK5) = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_28,c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1245,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.41/0.99      | k2_zfmisc_1(sK4,sK5) = X0 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_1221,c_28]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_22,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = X3 ),
% 3.41/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_522,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1),X2) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X2
% 3.41/0.99      | k1_xboole_0 = sK1 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1308,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),X1) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = sK1
% 3.41/0.99      | k1_xboole_0 = sK2 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_522]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1468,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),sK3) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = sK1
% 3.41/0.99      | k1_xboole_0 = sK2
% 3.41/0.99      | k1_xboole_0 = sK3 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1308]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2948,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = sK0
% 3.41/0.99      | k1_xboole_0 = sK1
% 3.41/0.99      | k1_xboole_0 = sK2
% 3.41/0.99      | k1_xboole_0 = sK3 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1468]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2977,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | k2_zfmisc_1(sK4,sK5) = X0 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1216,c_27,c_26,c_25,c_24,c_1245,c_2948]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2987,plain,
% 3.41/0.99      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_2977]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7198,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),X1) != k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2987,c_22]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_16,plain,
% 3.41/0.99      ( X0 = X1
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1058,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | sK6 = X1 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_28,c_16]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1631,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.41/0.99      | sK6 = sK2 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_1058]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_12,plain,
% 3.41/0.99      ( X0 = X1
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 3.41/0.99      | k1_xboole_0 = X5
% 3.41/0.99      | k1_xboole_0 = X4
% 3.41/0.99      | k1_xboole_0 = X1 ),
% 3.41/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2256,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | sK7 = X2
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_28,c_12]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_15,plain,
% 3.41/0.99      ( X0 = X1
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1005,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | sK7 = X2 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_28,c_15]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1028,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.41/0.99      | sK7 = X2 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_1005,c_28]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3323,plain,
% 3.41/0.99      ( sK7 = X2
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_2256,c_27,c_26,c_25,c_24,c_1028,c_2948]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3324,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.41/0.99      | sK7 = X2 ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_3323]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3333,plain,
% 3.41/0.99      ( sK7 = sK3 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_3324]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_23,negated_conjecture,
% 3.41/0.99      ( sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7 ),
% 3.41/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6589,plain,
% 3.41/0.99      ( sK4 != sK0 | sK5 != sK1 | sK6 != sK2 | sK3 != sK3 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_3333,c_23]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6593,plain,
% 3.41/0.99      ( sK4 != sK0 | sK5 != sK1 | sK6 != sK2 ),
% 3.41/0.99      inference(equality_resolution_simp,[status(thm)],[c_6589]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4,plain,
% 3.41/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2255,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = X2 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_4,c_12]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7194,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) != k1_xboole_0
% 3.41/0.99      | sK4 = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2987,c_2255]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7203,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.41/0.99      | sK4 = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2987,c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8177,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 | sK4 = sK0 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_7203]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7208,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
% 3.41/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.41/0.99      | sK5 = X1 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2987,c_16]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8354,plain,
% 3.41/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 | sK5 = sK1 ),
% 3.41/0.99      inference(equality_resolution,[status(thm)],[c_7208]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9349,plain,
% 3.41/0.99      ( sK5 = k1_xboole_0 | sK4 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_7198,c_27,c_26,c_25,c_24,c_1631,c_2948,c_6593,c_7194,
% 3.41/0.99                 c_8177,c_8354]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9350,plain,
% 3.41/0.99      ( sK4 = k1_xboole_0 | sK5 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_9349]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9595,plain,
% 3.41/0.99      ( k2_zfmisc_1(k1_xboole_0,sK5) = k2_zfmisc_1(sK0,sK1)
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_9350,c_2987]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5,plain,
% 3.41/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9613,plain,
% 3.41/0.99      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.41/0.99      | sK5 = k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_9595,c_5]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6,plain,
% 3.41/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X1
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_467,plain,
% 3.41/0.99      ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = X0
% 3.41/0.99      | k1_xboole_0 = sK1 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_592,plain,
% 3.41/0.99      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 3.41/0.99      | k1_xboole_0 = sK0
% 3.41/0.99      | k1_xboole_0 = sK1 ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_467]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9625,plain,
% 3.41/0.99      ( sK5 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_9613,c_27,c_26,c_592]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9869,plain,
% 3.41/0.99      ( k2_zfmisc_1(sK4,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
% 3.41/0.99      | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_9625,c_2987]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9879,plain,
% 3.41/0.99      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_9869,c_4]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9976,plain,
% 3.41/0.99      ( k1_xboole_0 = X0 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_9879,c_27,c_26,c_592]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_10020,plain,
% 3.41/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.41/0.99      inference(demodulation,[status(thm)],[c_9976,c_26]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_10022,plain,
% 3.41/0.99      ( $false ),
% 3.41/0.99      inference(equality_resolution_simp,[status(thm)],[c_10020]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ General
% 3.41/0.99  
% 3.41/0.99  abstr_ref_over_cycles:                  0
% 3.41/0.99  abstr_ref_under_cycles:                 0
% 3.41/0.99  gc_basic_clause_elim:                   0
% 3.41/0.99  forced_gc_time:                         0
% 3.41/0.99  parsing_time:                           0.008
% 3.41/0.99  unif_index_cands_time:                  0.
% 3.41/0.99  unif_index_add_time:                    0.
% 3.41/0.99  orderings_time:                         0.
% 3.41/0.99  out_proof_time:                         0.011
% 3.41/0.99  total_time:                             0.354
% 3.41/0.99  num_of_symbols:                         42
% 3.41/0.99  num_of_terms:                           15379
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing
% 3.41/0.99  
% 3.41/0.99  num_of_splits:                          0
% 3.41/0.99  num_of_split_atoms:                     0
% 3.41/0.99  num_of_reused_defs:                     0
% 3.41/0.99  num_eq_ax_congr_red:                    0
% 3.41/0.99  num_of_sem_filtered_clauses:            1
% 3.41/0.99  num_of_subtypes:                        0
% 3.41/0.99  monotx_restored_types:                  0
% 3.41/0.99  sat_num_of_epr_types:                   0
% 3.41/0.99  sat_num_of_non_cyclic_types:            0
% 3.41/0.99  sat_guarded_non_collapsed_types:        0
% 3.41/0.99  num_pure_diseq_elim:                    0
% 3.41/0.99  simp_replaced_by:                       0
% 3.41/0.99  res_preprocessed:                       121
% 3.41/0.99  prep_upred:                             0
% 3.41/0.99  prep_unflattend:                        0
% 3.41/0.99  smt_new_axioms:                         0
% 3.41/0.99  pred_elim_cands:                        1
% 3.41/0.99  pred_elim:                              0
% 3.41/0.99  pred_elim_cl:                           0
% 3.41/0.99  pred_elim_cycles:                       2
% 3.41/0.99  merged_defs:                            0
% 3.41/0.99  merged_defs_ncl:                        0
% 3.41/0.99  bin_hyper_res:                          0
% 3.41/0.99  prep_cycles:                            4
% 3.41/0.99  pred_elim_time:                         0.
% 3.41/0.99  splitting_time:                         0.
% 3.41/0.99  sem_filter_time:                        0.
% 3.41/0.99  monotx_time:                            0.001
% 3.41/0.99  subtype_inf_time:                       0.
% 3.41/0.99  
% 3.41/0.99  ------ Problem properties
% 3.41/0.99  
% 3.41/0.99  clauses:                                28
% 3.41/0.99  conjectures:                            6
% 3.41/0.99  epr:                                    8
% 3.41/0.99  horn:                                   18
% 3.41/0.99  ground:                                 6
% 3.41/0.99  unary:                                  13
% 3.41/0.99  binary:                                 2
% 3.41/0.99  lits:                                   65
% 3.41/0.99  lits_eq:                                50
% 3.41/0.99  fd_pure:                                0
% 3.41/0.99  fd_pseudo:                              0
% 3.41/0.99  fd_cond:                                4
% 3.41/0.99  fd_pseudo_cond:                         7
% 3.41/0.99  ac_symbols:                             0
% 3.41/0.99  
% 3.41/0.99  ------ Propositional Solver
% 3.41/0.99  
% 3.41/0.99  prop_solver_calls:                      29
% 3.41/0.99  prop_fast_solver_calls:                 1043
% 3.41/0.99  smt_solver_calls:                       0
% 3.41/0.99  smt_fast_solver_calls:                  0
% 3.41/0.99  prop_num_of_clauses:                    4865
% 3.41/0.99  prop_preprocess_simplified:             12395
% 3.41/0.99  prop_fo_subsumed:                       40
% 3.41/0.99  prop_solver_time:                       0.
% 3.41/0.99  smt_solver_time:                        0.
% 3.41/0.99  smt_fast_solver_time:                   0.
% 3.41/0.99  prop_fast_solver_time:                  0.
% 3.41/0.99  prop_unsat_core_time:                   0.
% 3.41/0.99  
% 3.41/0.99  ------ QBF
% 3.41/0.99  
% 3.41/0.99  qbf_q_res:                              0
% 3.41/0.99  qbf_num_tautologies:                    0
% 3.41/0.99  qbf_prep_cycles:                        0
% 3.41/0.99  
% 3.41/0.99  ------ BMC1
% 3.41/0.99  
% 3.41/0.99  bmc1_current_bound:                     -1
% 3.41/0.99  bmc1_last_solved_bound:                 -1
% 3.41/0.99  bmc1_unsat_core_size:                   -1
% 3.41/0.99  bmc1_unsat_core_parents_size:           -1
% 3.41/0.99  bmc1_merge_next_fun:                    0
% 3.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation
% 3.41/0.99  
% 3.41/0.99  inst_num_of_clauses:                    2452
% 3.41/0.99  inst_num_in_passive:                    1801
% 3.41/0.99  inst_num_in_active:                     489
% 3.41/0.99  inst_num_in_unprocessed:                162
% 3.41/0.99  inst_num_of_loops:                      490
% 3.41/0.99  inst_num_of_learning_restarts:          0
% 3.41/0.99  inst_num_moves_active_passive:          1
% 3.41/0.99  inst_lit_activity:                      0
% 3.41/0.99  inst_lit_activity_moves:                0
% 3.41/0.99  inst_num_tautologies:                   0
% 3.41/0.99  inst_num_prop_implied:                  0
% 3.41/0.99  inst_num_existing_simplified:           0
% 3.41/0.99  inst_num_eq_res_simplified:             0
% 3.41/0.99  inst_num_child_elim:                    0
% 3.41/0.99  inst_num_of_dismatching_blockings:      5
% 3.41/0.99  inst_num_of_non_proper_insts:           1329
% 3.41/0.99  inst_num_of_duplicates:                 0
% 3.41/0.99  inst_inst_num_from_inst_to_res:         0
% 3.41/0.99  inst_dismatching_checking_time:         0.
% 3.41/0.99  
% 3.41/0.99  ------ Resolution
% 3.41/0.99  
% 3.41/0.99  res_num_of_clauses:                     0
% 3.41/0.99  res_num_in_passive:                     0
% 3.41/0.99  res_num_in_active:                      0
% 3.41/0.99  res_num_of_loops:                       125
% 3.41/0.99  res_forward_subset_subsumed:            30
% 3.41/0.99  res_backward_subset_subsumed:           0
% 3.41/0.99  res_forward_subsumed:                   0
% 3.41/0.99  res_backward_subsumed:                  0
% 3.41/0.99  res_forward_subsumption_resolution:     0
% 3.41/0.99  res_backward_subsumption_resolution:    0
% 3.41/0.99  res_clause_to_clause_subsumption:       1569
% 3.41/0.99  res_orphan_elimination:                 0
% 3.41/0.99  res_tautology_del:                      1
% 3.41/0.99  res_num_eq_res_simplified:              0
% 3.41/0.99  res_num_sel_changes:                    0
% 3.41/0.99  res_moves_from_active_to_pass:          0
% 3.41/0.99  
% 3.41/0.99  ------ Superposition
% 3.41/0.99  
% 3.41/0.99  sup_time_total:                         0.
% 3.41/0.99  sup_time_generating:                    0.
% 3.41/0.99  sup_time_sim_full:                      0.
% 3.41/0.99  sup_time_sim_immed:                     0.
% 3.41/0.99  
% 3.41/0.99  sup_num_of_clauses:                     124
% 3.41/0.99  sup_num_in_active:                      5
% 3.41/0.99  sup_num_in_passive:                     119
% 3.41/0.99  sup_num_of_loops:                       96
% 3.41/0.99  sup_fw_superposition:                   372
% 3.41/0.99  sup_bw_superposition:                   568
% 3.41/0.99  sup_immediate_simplified:               561
% 3.41/0.99  sup_given_eliminated:                   3
% 3.41/0.99  comparisons_done:                       0
% 3.41/0.99  comparisons_avoided:                    0
% 3.41/0.99  
% 3.41/0.99  ------ Simplifications
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  sim_fw_subset_subsumed:                 420
% 3.41/0.99  sim_bw_subset_subsumed:                 24
% 3.41/0.99  sim_fw_subsumed:                        59
% 3.41/0.99  sim_bw_subsumed:                        4
% 3.41/0.99  sim_fw_subsumption_res:                 0
% 3.41/0.99  sim_bw_subsumption_res:                 0
% 3.41/0.99  sim_tautology_del:                      64
% 3.41/0.99  sim_eq_tautology_del:                   127
% 3.41/0.99  sim_eq_res_simp:                        3
% 3.41/0.99  sim_fw_demodulated:                     71
% 3.41/0.99  sim_bw_demodulated:                     81
% 3.41/0.99  sim_light_normalised:                   70
% 3.41/0.99  sim_joinable_taut:                      0
% 3.41/0.99  sim_joinable_simp:                      0
% 3.41/0.99  sim_ac_normalised:                      0
% 3.41/0.99  sim_smt_subsumption:                    0
% 3.41/0.99  
%------------------------------------------------------------------------------
