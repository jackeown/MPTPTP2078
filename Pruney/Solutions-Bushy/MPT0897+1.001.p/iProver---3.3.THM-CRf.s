%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0897+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:22 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 605 expanded)
%              Number of clauses        :   68 ( 189 expanded)
%              Number of leaves         :    5 ( 117 expanded)
%              Depth                    :   33
%              Number of atoms          :  386 (3151 expanded)
%              Number of equality atoms :  385 (3150 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f11])).

fof(f22,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
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

fof(f5,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f5])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f14])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X2 = X6
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X1 = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X3 = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f15])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3) ),
    inference(equality_resolution,[],[f16])).

fof(f24,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f17])).

cnf(c_11,negated_conjecture,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8,plain,
    ( X0 = X1
    | k4_zfmisc_1(X0,X2,X3,X4) != k4_zfmisc_1(X1,X5,X6,X7)
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_546,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK4 = X0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_924,plain,
    ( sK4 = sK0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_546])).

cnf(c_1742,plain,
    ( k4_zfmisc_1(sK0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_924,c_11])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_13,plain,
    ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k4_zfmisc_1(k1_xboole_0,X0,X1,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,plain,
    ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_19,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_103,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_104,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_6,plain,
    ( X0 = X1
    | k4_zfmisc_1(X2,X3,X0,X4) != k4_zfmisc_1(X5,X6,X1,X7)
    | k1_xboole_0 = X7
    | k1_xboole_0 = X1
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_393,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = X2
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_6])).

cnf(c_734,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = sK2
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_393])).

cnf(c_1546,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK5 = k1_xboole_0
    | sK6 = sK2
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_734,c_11])).

cnf(c_1552,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = sK2
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1546,c_3])).

cnf(c_7,plain,
    ( X0 = X1
    | k4_zfmisc_1(X2,X0,X3,X4) != k4_zfmisc_1(X5,X1,X6,X7)
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X1
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_440,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK4 = k1_xboole_0
    | sK5 = X1
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_7])).

cnf(c_832,plain,
    ( sK4 = k1_xboole_0
    | sK5 = sK1
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_440])).

cnf(c_1708,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK5 = sK1
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_832,c_11])).

cnf(c_1714,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK5 = sK1
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1708,c_3])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_zfmisc_1(X2,X3,X4,X0) != k4_zfmisc_1(X5,X6,X7,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X7
    | k1_xboole_0 = X6
    | k1_xboole_0 = X5 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_314,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = X3
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_5])).

cnf(c_648,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_314])).

cnf(c_1326,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_11])).

cnf(c_1332,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1326,c_3])).

cnf(c_1889,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_10,c_13,c_14,c_104])).

cnf(c_1896,plain,
    ( k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1889,c_11])).

cnf(c_2,plain,
    ( k4_zfmisc_1(X0,k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1901,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1896,c_2])).

cnf(c_1970,plain,
    ( sK6 = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_10,c_13,c_14,c_104])).

cnf(c_1976,plain,
    ( k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1970,c_11])).

cnf(c_1,plain,
    ( k4_zfmisc_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1980,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1976,c_1])).

cnf(c_1989,plain,
    ( sK7 = sK3
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_10,c_13,c_14,c_104])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1993,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1989,c_9])).

cnf(c_2161,plain,
    ( sK4 = k1_xboole_0
    | sK5 != sK1
    | sK5 = k1_xboole_0
    | sK6 != sK2
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_924,c_1993])).

cnf(c_2222,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_10,c_13,c_14,c_104,c_1552,c_1714,c_2161])).

cnf(c_2234,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2222,c_11])).

cnf(c_2239,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2234,c_3])).

cnf(c_2281,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_10,c_13,c_14,c_104])).

cnf(c_2288,plain,
    ( k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2281,c_11])).

cnf(c_2292,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2288,c_2])).

cnf(c_2346,plain,
    ( sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2292,c_10,c_13,c_14,c_104])).

cnf(c_2352,plain,
    ( k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7) = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2346,c_11])).

cnf(c_2355,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2352,c_1])).

cnf(c_2365,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2355,c_10,c_13,c_14,c_104])).

cnf(c_309,plain,
    ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | sK7 = X3
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_11,c_5])).

cnf(c_589,plain,
    ( sK0 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_309])).

cnf(c_249,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_4])).

cnf(c_296,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_10,c_13,c_14,c_104])).

cnf(c_948,plain,
    ( k4_zfmisc_1(k1_xboole_0,sK1,sK2,sK3) != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_589,c_296])).

cnf(c_955,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_948,c_3])).

cnf(c_956,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_955])).

cnf(c_1019,plain,
    ( k4_zfmisc_1(sK0,k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_956,c_296])).

cnf(c_1025,plain,
    ( sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1019,c_2])).

cnf(c_1026,plain,
    ( sK2 = k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1025])).

cnf(c_1047,plain,
    ( k4_zfmisc_1(sK0,sK1,k1_xboole_0,sK3) != k1_xboole_0
    | sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1026,c_296])).

cnf(c_1052,plain,
    ( sK7 = sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1047,c_1])).

cnf(c_1053,plain,
    ( sK7 = sK3
    | sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1052])).

cnf(c_2373,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2365,c_1053])).

cnf(c_2480,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2373,c_296])).

cnf(c_0,plain,
    ( k4_zfmisc_1(X0,X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2483,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2480,c_0])).

cnf(c_2484,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2483])).


%------------------------------------------------------------------------------
