%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0878+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 35.13s
% Output     : CNFRefutation 35.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 171 expanded)
%              Number of clauses        :   19 (  35 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 355 expanded)
%              Number of equality atoms :  115 ( 354 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1324,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1325,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1324])).

fof(f2679,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f1325])).

fof(f3694,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK379 != sK380
      & k3_zfmisc_1(sK379,sK379,sK379) = k3_zfmisc_1(sK380,sK380,sK380) ) ),
    introduced(choice_axiom,[])).

fof(f3695,plain,
    ( sK379 != sK380
    & k3_zfmisc_1(sK379,sK379,sK379) = k3_zfmisc_1(sK380,sK380,sK380) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK379,sK380])],[f2679,f3694])).

fof(f6026,plain,(
    k3_zfmisc_1(sK379,sK379,sK379) = k3_zfmisc_1(sK380,sK380,sK380) ),
    inference(cnf_transformation,[],[f3695])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5903,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6781,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) = k2_zfmisc_1(k2_zfmisc_1(sK380,sK380),sK380) ),
    inference(definition_unfolding,[],[f6026,f5903,f5903])).

fof(f1323,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2677,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1323])).

fof(f2678,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f2677])).

fof(f6024,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2678])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3713,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6779,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6024,f3713,f5903,f5903,f5903])).

fof(f6027,plain,(
    sK379 != sK380 ),
    inference(cnf_transformation,[],[f3695])).

fof(f6025,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f2678])).

fof(f6778,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f6025,f3713,f5903,f5903,f5903])).

fof(f1321,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3692,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1321])).

fof(f3693,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f3692])).

fof(f6016,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3693])).

fof(f6774,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6016,f3713,f5903,f3713,f3713,f3713])).

cnf(c_2303,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) = k2_zfmisc_1(k2_zfmisc_1(sK380,sK380),sK380) ),
    inference(cnf_transformation,[],[f6781])).

cnf(c_2300,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6779])).

cnf(c_110135,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379)
    | k2_zfmisc_1(k2_zfmisc_1(sK380,sK380),sK380) = o_0_0_xboole_0
    | sK380 = X1 ),
    inference(superposition,[status(thm)],[c_2303,c_2300])).

cnf(c_110244,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379)
    | k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) = o_0_0_xboole_0
    | sK380 = X1 ),
    inference(demodulation,[status(thm)],[c_110135,c_2303])).

cnf(c_2302,negated_conjecture,
    ( sK379 != sK380 ),
    inference(cnf_transformation,[],[f6027])).

cnf(c_2299,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6778])).

cnf(c_109913,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = o_0_0_xboole_0
    | sK380 = X2 ),
    inference(superposition,[status(thm)],[c_2303,c_2299])).

cnf(c_111307,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) = o_0_0_xboole_0
    | sK380 = sK379 ),
    inference(equality_resolution,[status(thm)],[c_109913])).

cnf(c_32624,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_86552,plain,
    ( sK380 != X0
    | sK379 != X0
    | sK379 = sK380 ),
    inference(instantiation,[status(thm)],[c_32624])).

cnf(c_113328,plain,
    ( sK380 != sK379
    | sK379 = sK380
    | sK379 != sK379 ),
    inference(instantiation,[status(thm)],[c_86552])).

cnf(c_32623,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_113329,plain,
    ( sK379 = sK379 ),
    inference(instantiation,[status(thm)],[c_32623])).

cnf(c_113692,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_110244,c_2302,c_111307,c_113328,c_113329])).

cnf(c_2295,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f6774])).

cnf(c_113888,plain,
    ( sK379 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_113692,c_2295])).

cnf(c_104574,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK379,sK379),sK379) != o_0_0_xboole_0
    | sK380 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2303,c_2295])).

cnf(c_86553,plain,
    ( sK380 != o_0_0_xboole_0
    | sK379 = sK380
    | sK379 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_86552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113888,c_113329,c_113328,c_111307,c_104574,c_86553,c_2302])).

%------------------------------------------------------------------------------
