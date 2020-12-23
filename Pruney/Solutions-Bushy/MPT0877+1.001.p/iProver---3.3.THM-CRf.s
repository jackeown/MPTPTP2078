%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:19 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 300 expanded)
%              Number of clauses        :   40 (  92 expanded)
%              Number of leaves         :    5 (  59 expanded)
%              Depth                    :   25
%              Number of atoms          :  224 (1293 expanded)
%              Number of equality atoms :  223 (1292 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f11])).

fof(f20,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f5])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f14])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f15])).

fof(f22,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

cnf(c_9,negated_conjecture,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( X0 = X1
    | k3_zfmisc_1(X0,X2,X3) != k3_zfmisc_1(X1,X4,X5)
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_396,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 = X0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_653,plain,
    ( sK3 = sK0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_396])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_11,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k3_zfmisc_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_78,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_79,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_5,plain,
    ( X0 = X1
    | k3_zfmisc_1(X2,X0,X3) != k3_zfmisc_1(X4,X1,X5)
    | k1_xboole_0 = X5
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_319,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 = k1_xboole_0
    | sK4 = X1
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_5])).

cnf(c_588,plain,
    ( sK3 = k1_xboole_0
    | sK4 = sK1
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_319])).

cnf(c_819,plain,
    ( k3_zfmisc_1(k1_xboole_0,sK4,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | sK4 = sK1
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_9])).

cnf(c_824,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK4 = sK1
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_819,c_2])).

cnf(c_4,plain,
    ( X0 = X1
    | k3_zfmisc_1(X2,X3,X0) != k3_zfmisc_1(X4,X5,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_279,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = X2
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_504,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_279])).

cnf(c_723,plain,
    ( k3_zfmisc_1(k1_xboole_0,sK4,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | sK4 = k1_xboole_0
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_504,c_9])).

cnf(c_728,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_723,c_2])).

cnf(c_955,plain,
    ( sK4 = k1_xboole_0
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_8,c_11,c_12,c_79])).

cnf(c_960,plain,
    ( k3_zfmisc_1(sK3,k1_xboole_0,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_955,c_9])).

cnf(c_1,plain,
    ( k3_zfmisc_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_961,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_960,c_1])).

cnf(c_962,plain,
    ( sK5 = sK2
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_961,c_8,c_11,c_12,c_79])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_966,plain,
    ( sK3 != sK0
    | sK4 != sK1
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_962,c_7])).

cnf(c_1460,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_8,c_11,c_12,c_79,c_824,c_966])).

cnf(c_1469,plain,
    ( k3_zfmisc_1(k1_xboole_0,sK4,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1460,c_9])).

cnf(c_1473,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1469,c_2])).

cnf(c_1560,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_8,c_11,c_12,c_79])).

cnf(c_1566,plain,
    ( k3_zfmisc_1(sK3,k1_xboole_0,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1560,c_9])).

cnf(c_1569,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1566,c_1])).

cnf(c_1586,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1569,c_8,c_11,c_12,c_79])).

cnf(c_1599,plain,
    ( k3_zfmisc_1(sK3,sK4,k1_xboole_0) = k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1586,c_9])).

cnf(c_0,plain,
    ( k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1601,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1599,c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1601,c_79,c_12,c_11,c_8])).


%------------------------------------------------------------------------------
