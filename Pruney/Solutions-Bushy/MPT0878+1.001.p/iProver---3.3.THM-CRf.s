%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0878+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:19 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   25 (  44 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 137 expanded)
%              Number of equality atoms :   73 ( 136 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f12,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f4])).

fof(f11,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_4,negated_conjecture,
    ( k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( X0 = X1
    | k3_zfmisc_1(X2,X3,X0) != k3_zfmisc_1(X4,X5,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X5
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_86,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK0,sK0)
    | sK1 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_132,plain,
    ( sK1 = sK0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_86])).

cnf(c_9,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_122,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_48,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_121,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_87,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK0,sK0)
    | sK1 = X2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_110,plain,
    ( sK1 = sK0
    | sK1 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_87])).

cnf(c_49,plain,
    ( sK1 != k1_xboole_0
    | sK0 = sK1
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_3,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_132,c_122,c_121,c_110,c_49,c_3])).


%------------------------------------------------------------------------------
