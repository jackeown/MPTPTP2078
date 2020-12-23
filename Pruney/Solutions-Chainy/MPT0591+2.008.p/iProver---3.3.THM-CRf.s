%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:12 EST 2020

% Result     : Theorem 19.41s
% Output     : CNFRefutation 19.41s
% Verified   : 
% Statistics : Number of formulae       :  196 (10469 expanded)
%              Number of clauses        :  148 (2999 expanded)
%              Number of leaves         :   15 (3031 expanded)
%              Depth                    :   26
%              Number of atoms          :  582 (46097 expanded)
%              Number of equality atoms :  341 (14306 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7
        | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 )
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7
      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 )
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f7,f24])).

fof(f42,plain,
    ( k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f31])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f41,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2725,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,X1))) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3622,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X3))
    | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,X3))) ),
    inference(resolution,[status(thm)],[c_2725,c_9])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3075,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X2)
    | r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X1)
    | k2_relat_1(k2_zfmisc_1(X0,X1)) = X2 ),
    inference(resolution,[status(thm)],[c_11,c_1])).

cnf(c_14,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11778,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
    inference(resolution,[status(thm)],[c_3075,c_14])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1888,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2)
    | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X0)
    | k1_relat_1(k2_zfmisc_1(X0,X1)) = X2 ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_12523,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(resolution,[status(thm)],[c_11778,c_1888])).

cnf(c_13180,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,sK7)))
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(resolution,[status(thm)],[c_12523,c_2725])).

cnf(c_24860,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X3,sK7))))
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(resolution,[status(thm)],[c_3622,c_13180])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_120,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_557,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_121,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_462,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_665,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_1088,plain,
    ( k1_relat_1(X0) != sK6
    | sK6 = k1_relat_1(X0)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1089,plain,
    ( k1_relat_1(k1_xboole_0) != sK6
    | sK6 = k1_relat_1(k1_xboole_0)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_307,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_309,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_739,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_309])).

cnf(c_1330,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_307,c_739])).

cnf(c_1402,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X0)
    | r2_hidden(sK0(k1_xboole_0,X0),X1)
    | k1_relat_1(k1_xboole_0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1330])).

cnf(c_1404,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_305,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_308,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1),X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1447,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_308])).

cnf(c_1465,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1447])).

cnf(c_1467,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_2096,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_2097,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4968,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(k2_zfmisc_1(X1,X2),X3),X3)
    | ~ r2_hidden(sK3(k2_zfmisc_1(X1,X2),X3),X2)
    | k2_relat_1(k2_zfmisc_1(X1,X2)) = X3 ),
    inference(resolution,[status(thm)],[c_10,c_0])).

cnf(c_16202,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
    inference(resolution,[status(thm)],[c_4968,c_12523])).

cnf(c_443,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK1(k2_zfmisc_1(sK6,sK7),sK6)),k2_zfmisc_1(sK6,sK7))
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1036,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK1(k2_zfmisc_1(sK6,sK7),sK6)),k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17023,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | ~ r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16202,c_14,c_443,c_1036,c_12523])).

cnf(c_17024,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(renaming,[status(thm)],[c_17023])).

cnf(c_1757,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_17041,plain,
    ( r2_hidden(sK0(X0,sK6),k1_relat_1(X0))
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | k1_relat_1(X0) = sK6 ),
    inference(resolution,[status(thm)],[c_17024,c_1757])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2742,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_124,c_4])).

cnf(c_4989,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2742,c_120])).

cnf(c_5490,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4989,c_1])).

cnf(c_5520,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(sK2(k1_xboole_0,X0),X1) ),
    inference(resolution,[status(thm)],[c_5490,c_9])).

cnf(c_17103,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(resolution,[status(thm)],[c_17024,c_5520])).

cnf(c_21575,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | k1_relat_1(k1_xboole_0) = sK6 ),
    inference(resolution,[status(thm)],[c_17041,c_17103])).

cnf(c_306,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1328,plain,
    ( k1_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_307,c_306])).

cnf(c_311,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1445,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X2
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_311,c_308])).

cnf(c_25944,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK0(k2_zfmisc_1(k1_xboole_0,X0),X1),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1445])).

cnf(c_25949,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25944,c_4])).

cnf(c_5178,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1330])).

cnf(c_5180,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5178])).

cnf(c_26280,plain,
    ( r2_hidden(X1,X2) != iProver_top
    | k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25949,c_5180])).

cnf(c_26281,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_26280])).

cnf(c_26288,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1328,c_26281])).

cnf(c_26304,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26288])).

cnf(c_431,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_27990,plain,
    ( sK6 != k1_relat_1(X0)
    | k1_xboole_0 != k1_relat_1(X0)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_27991,plain,
    ( sK6 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_27990])).

cnf(c_31796,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24860,c_16,c_41,c_42,c_557,c_1089,c_1404,c_1467,c_2097,c_21575,c_26304,c_27991])).

cnf(c_32558,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_31796,c_12523])).

cnf(c_4952,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_zfmisc_1(X2,X1),X3),X3)
    | ~ r2_hidden(sK0(k2_zfmisc_1(X2,X1),X3),X2)
    | k1_relat_1(k2_zfmisc_1(X2,X1)) = X3 ),
    inference(resolution,[status(thm)],[c_6,c_0])).

cnf(c_32847,plain,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(resolution,[status(thm)],[c_32558,c_4952])).

cnf(c_33308,plain,
    ( ~ r2_hidden(X0,sK7)
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32847,c_32558])).

cnf(c_11864,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(X0,X1),X1),X1)
    | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ),
    inference(factoring,[status(thm)],[c_3075])).

cnf(c_33413,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,sK7)) = sK7
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(resolution,[status(thm)],[c_33308,c_11864])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),X0),k2_zfmisc_1(sK6,X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1665,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
    | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_492,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | ~ r2_hidden(k4_tarski(X0,sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7))
    | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_41651,plain,
    ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
    | ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7))
    | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_58942,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33413,c_14,c_1665,c_11778,c_32558,c_41651])).

cnf(c_58949,plain,
    ( k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_58942,c_14])).

cnf(c_2738,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_124,c_3])).

cnf(c_3977,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2738,c_120])).

cnf(c_4027,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3977,c_2])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4528,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | r2_hidden(sK5(k1_xboole_0,X0),X1) ),
    inference(resolution,[status(thm)],[c_4027,c_13])).

cnf(c_33374,plain,
    ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(resolution,[status(thm)],[c_33308,c_4528])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3081,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0))
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_40647,plain,
    ( r2_hidden(sK3(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(resolution,[status(thm)],[c_33374,c_3081])).

cnf(c_59900,plain,
    ( r2_hidden(sK3(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_58949,c_40647])).

cnf(c_59791,plain,
    ( ~ r2_hidden(X0,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_58949,c_33308])).

cnf(c_91456,plain,
    ( k2_relat_1(k1_xboole_0) = sK7 ),
    inference(resolution,[status(thm)],[c_59900,c_59791])).

cnf(c_303,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_737,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X2
    | r2_hidden(sK4(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_309])).

cnf(c_3161,plain,
    ( k2_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = X1
    | r2_hidden(sK4(k1_xboole_0,X1),k1_xboole_0) = iProver_top
    | r2_hidden(sK3(k2_zfmisc_1(k1_xboole_0,X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_737])).

cnf(c_3285,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3161,c_4])).

cnf(c_614,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_306])).

cnf(c_1110,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_311])).

cnf(c_1941,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_1110])).

cnf(c_301,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_304,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_946,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_301,c_304])).

cnf(c_302,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_615,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_302])).

cnf(c_2423,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_1110])).

cnf(c_2427,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_1110])).

cnf(c_57735,plain,
    ( r2_hidden(X2,k1_xboole_0) != iProver_top
    | k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_946,c_2423,c_2427])).

cnf(c_57736,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_57735])).

cnf(c_1111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_311])).

cnf(c_1940,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_1111])).

cnf(c_2422,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_1111])).

cnf(c_2426,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_1111])).

cnf(c_55607,plain,
    ( r2_hidden(X2,k1_xboole_0) != iProver_top
    | k2_relat_1(X0) = X1
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1940,c_946,c_2422,c_2426])).

cnf(c_55608,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_55607])).

cnf(c_1114,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_311,c_306])).

cnf(c_55618,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,k1_xboole_0))) = iProver_top
    | r2_hidden(X4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_55608,c_1114])).

cnf(c_55718,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X2,k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(X4,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_55618,c_3])).

cnf(c_310,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_866,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_310])).

cnf(c_964,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK2(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_866])).

cnf(c_1854,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_1111])).

cnf(c_33386,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
    inference(resolution,[status(thm)],[c_33308,c_5520])).

cnf(c_33387,plain,
    ( k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33386])).

cnf(c_51269,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1854,c_14,c_1665,c_11778,c_32558,c_33387,c_41651])).

cnf(c_57047,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X4,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_55718,c_51269])).

cnf(c_57742,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57736,c_57047])).

cnf(c_57757,plain,
    ( k2_relat_1(X0) = X1
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3285,c_57742])).

cnf(c_57945,plain,
    ( k2_relat_1(X0) = X1
    | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57757,c_57742])).

cnf(c_58760,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_57945])).

cnf(c_22802,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_22803,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22802])).

cnf(c_429,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_2340,plain,
    ( sK7 != k2_relat_1(X0)
    | k1_xboole_0 != k2_relat_1(X0)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_2341,plain,
    ( sK7 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2340])).

cnf(c_460,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_600,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1056,plain,
    ( k2_relat_1(X0) != sK7
    | sK7 = k2_relat_1(X0)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1059,plain,
    ( k2_relat_1(k1_xboole_0) != sK7
    | sK7 = k2_relat_1(k1_xboole_0)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_601,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91456,c_58760,c_22803,c_2341,c_1059,c_601,c_42,c_41,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:13:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.41/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.41/2.98  
% 19.41/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.41/2.98  
% 19.41/2.98  ------  iProver source info
% 19.41/2.98  
% 19.41/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.41/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.41/2.98  git: non_committed_changes: false
% 19.41/2.98  git: last_make_outside_of_git: false
% 19.41/2.98  
% 19.41/2.98  ------ 
% 19.41/2.98  
% 19.41/2.98  ------ Input Options
% 19.41/2.98  
% 19.41/2.98  --out_options                           all
% 19.41/2.98  --tptp_safe_out                         true
% 19.41/2.98  --problem_path                          ""
% 19.41/2.98  --include_path                          ""
% 19.41/2.98  --clausifier                            res/vclausify_rel
% 19.41/2.98  --clausifier_options                    --mode clausify
% 19.41/2.98  --stdin                                 false
% 19.41/2.98  --stats_out                             sel
% 19.41/2.98  
% 19.41/2.98  ------ General Options
% 19.41/2.98  
% 19.41/2.98  --fof                                   false
% 19.41/2.98  --time_out_real                         604.99
% 19.41/2.98  --time_out_virtual                      -1.
% 19.41/2.98  --symbol_type_check                     false
% 19.41/2.98  --clausify_out                          false
% 19.41/2.98  --sig_cnt_out                           false
% 19.41/2.98  --trig_cnt_out                          false
% 19.41/2.98  --trig_cnt_out_tolerance                1.
% 19.41/2.98  --trig_cnt_out_sk_spl                   false
% 19.41/2.98  --abstr_cl_out                          false
% 19.41/2.98  
% 19.41/2.98  ------ Global Options
% 19.41/2.98  
% 19.41/2.98  --schedule                              none
% 19.41/2.98  --add_important_lit                     false
% 19.41/2.98  --prop_solver_per_cl                    1000
% 19.41/2.98  --min_unsat_core                        false
% 19.41/2.98  --soft_assumptions                      false
% 19.41/2.98  --soft_lemma_size                       3
% 19.41/2.98  --prop_impl_unit_size                   0
% 19.41/2.98  --prop_impl_unit                        []
% 19.41/2.98  --share_sel_clauses                     true
% 19.41/2.98  --reset_solvers                         false
% 19.41/2.98  --bc_imp_inh                            [conj_cone]
% 19.41/2.98  --conj_cone_tolerance                   3.
% 19.41/2.98  --extra_neg_conj                        none
% 19.41/2.98  --large_theory_mode                     true
% 19.41/2.98  --prolific_symb_bound                   200
% 19.41/2.98  --lt_threshold                          2000
% 19.41/2.98  --clause_weak_htbl                      true
% 19.41/2.98  --gc_record_bc_elim                     false
% 19.41/2.98  
% 19.41/2.98  ------ Preprocessing Options
% 19.41/2.98  
% 19.41/2.98  --preprocessing_flag                    true
% 19.41/2.98  --time_out_prep_mult                    0.1
% 19.41/2.98  --splitting_mode                        input
% 19.41/2.98  --splitting_grd                         true
% 19.41/2.98  --splitting_cvd                         false
% 19.41/2.98  --splitting_cvd_svl                     false
% 19.41/2.98  --splitting_nvd                         32
% 19.41/2.98  --sub_typing                            true
% 19.41/2.98  --prep_gs_sim                           false
% 19.41/2.98  --prep_unflatten                        true
% 19.41/2.98  --prep_res_sim                          true
% 19.41/2.98  --prep_upred                            true
% 19.41/2.98  --prep_sem_filter                       exhaustive
% 19.41/2.98  --prep_sem_filter_out                   false
% 19.41/2.98  --pred_elim                             false
% 19.41/2.98  --res_sim_input                         true
% 19.41/2.98  --eq_ax_congr_red                       true
% 19.41/2.98  --pure_diseq_elim                       true
% 19.41/2.98  --brand_transform                       false
% 19.41/2.98  --non_eq_to_eq                          false
% 19.41/2.98  --prep_def_merge                        true
% 19.41/2.98  --prep_def_merge_prop_impl              false
% 19.41/2.98  --prep_def_merge_mbd                    true
% 19.41/2.98  --prep_def_merge_tr_red                 false
% 19.41/2.98  --prep_def_merge_tr_cl                  false
% 19.41/2.98  --smt_preprocessing                     true
% 19.41/2.98  --smt_ac_axioms                         fast
% 19.41/2.98  --preprocessed_out                      false
% 19.41/2.98  --preprocessed_stats                    false
% 19.41/2.98  
% 19.41/2.98  ------ Abstraction refinement Options
% 19.41/2.98  
% 19.41/2.98  --abstr_ref                             []
% 19.41/2.98  --abstr_ref_prep                        false
% 19.41/2.98  --abstr_ref_until_sat                   false
% 19.41/2.98  --abstr_ref_sig_restrict                funpre
% 19.41/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.41/2.98  --abstr_ref_under                       []
% 19.41/2.98  
% 19.41/2.98  ------ SAT Options
% 19.41/2.98  
% 19.41/2.98  --sat_mode                              false
% 19.41/2.98  --sat_fm_restart_options                ""
% 19.41/2.98  --sat_gr_def                            false
% 19.41/2.98  --sat_epr_types                         true
% 19.41/2.98  --sat_non_cyclic_types                  false
% 19.41/2.98  --sat_finite_models                     false
% 19.41/2.98  --sat_fm_lemmas                         false
% 19.41/2.98  --sat_fm_prep                           false
% 19.41/2.98  --sat_fm_uc_incr                        true
% 19.41/2.98  --sat_out_model                         small
% 19.41/2.98  --sat_out_clauses                       false
% 19.41/2.98  
% 19.41/2.98  ------ QBF Options
% 19.41/2.98  
% 19.41/2.98  --qbf_mode                              false
% 19.41/2.98  --qbf_elim_univ                         false
% 19.41/2.98  --qbf_dom_inst                          none
% 19.41/2.98  --qbf_dom_pre_inst                      false
% 19.41/2.98  --qbf_sk_in                             false
% 19.41/2.98  --qbf_pred_elim                         true
% 19.41/2.98  --qbf_split                             512
% 19.41/2.98  
% 19.41/2.98  ------ BMC1 Options
% 19.41/2.98  
% 19.41/2.98  --bmc1_incremental                      false
% 19.41/2.98  --bmc1_axioms                           reachable_all
% 19.41/2.98  --bmc1_min_bound                        0
% 19.41/2.98  --bmc1_max_bound                        -1
% 19.41/2.98  --bmc1_max_bound_default                -1
% 19.41/2.98  --bmc1_symbol_reachability              true
% 19.41/2.98  --bmc1_property_lemmas                  false
% 19.41/2.98  --bmc1_k_induction                      false
% 19.41/2.98  --bmc1_non_equiv_states                 false
% 19.41/2.98  --bmc1_deadlock                         false
% 19.41/2.98  --bmc1_ucm                              false
% 19.41/2.98  --bmc1_add_unsat_core                   none
% 19.41/2.98  --bmc1_unsat_core_children              false
% 19.41/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.41/2.98  --bmc1_out_stat                         full
% 19.41/2.98  --bmc1_ground_init                      false
% 19.41/2.98  --bmc1_pre_inst_next_state              false
% 19.41/2.98  --bmc1_pre_inst_state                   false
% 19.41/2.98  --bmc1_pre_inst_reach_state             false
% 19.41/2.98  --bmc1_out_unsat_core                   false
% 19.41/2.98  --bmc1_aig_witness_out                  false
% 19.41/2.98  --bmc1_verbose                          false
% 19.41/2.98  --bmc1_dump_clauses_tptp                false
% 19.41/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.41/2.98  --bmc1_dump_file                        -
% 19.41/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.41/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.41/2.98  --bmc1_ucm_extend_mode                  1
% 19.41/2.98  --bmc1_ucm_init_mode                    2
% 19.41/2.98  --bmc1_ucm_cone_mode                    none
% 19.41/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.41/2.98  --bmc1_ucm_relax_model                  4
% 19.41/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.41/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.41/2.98  --bmc1_ucm_layered_model                none
% 19.41/2.98  --bmc1_ucm_max_lemma_size               10
% 19.41/2.98  
% 19.41/2.98  ------ AIG Options
% 19.41/2.98  
% 19.41/2.98  --aig_mode                              false
% 19.41/2.98  
% 19.41/2.98  ------ Instantiation Options
% 19.41/2.98  
% 19.41/2.98  --instantiation_flag                    true
% 19.41/2.98  --inst_sos_flag                         false
% 19.41/2.98  --inst_sos_phase                        true
% 19.41/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.41/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.41/2.98  --inst_lit_sel_side                     num_symb
% 19.41/2.98  --inst_solver_per_active                1400
% 19.41/2.98  --inst_solver_calls_frac                1.
% 19.41/2.98  --inst_passive_queue_type               priority_queues
% 19.41/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.41/2.98  --inst_passive_queues_freq              [25;2]
% 19.41/2.98  --inst_dismatching                      true
% 19.41/2.98  --inst_eager_unprocessed_to_passive     true
% 19.41/2.98  --inst_prop_sim_given                   true
% 19.41/2.98  --inst_prop_sim_new                     false
% 19.41/2.98  --inst_subs_new                         false
% 19.41/2.98  --inst_eq_res_simp                      false
% 19.41/2.98  --inst_subs_given                       false
% 19.41/2.98  --inst_orphan_elimination               true
% 19.41/2.98  --inst_learning_loop_flag               true
% 19.41/2.98  --inst_learning_start                   3000
% 19.41/2.98  --inst_learning_factor                  2
% 19.41/2.98  --inst_start_prop_sim_after_learn       3
% 19.41/2.98  --inst_sel_renew                        solver
% 19.41/2.98  --inst_lit_activity_flag                true
% 19.41/2.98  --inst_restr_to_given                   false
% 19.41/2.98  --inst_activity_threshold               500
% 19.41/2.98  --inst_out_proof                        true
% 19.41/2.98  
% 19.41/2.98  ------ Resolution Options
% 19.41/2.98  
% 19.41/2.98  --resolution_flag                       true
% 19.41/2.98  --res_lit_sel                           adaptive
% 19.41/2.98  --res_lit_sel_side                      none
% 19.41/2.98  --res_ordering                          kbo
% 19.41/2.98  --res_to_prop_solver                    active
% 19.41/2.98  --res_prop_simpl_new                    false
% 19.41/2.98  --res_prop_simpl_given                  true
% 19.41/2.98  --res_passive_queue_type                priority_queues
% 19.41/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.41/2.98  --res_passive_queues_freq               [15;5]
% 19.41/2.98  --res_forward_subs                      full
% 19.41/2.98  --res_backward_subs                     full
% 19.41/2.98  --res_forward_subs_resolution           true
% 19.41/2.98  --res_backward_subs_resolution          true
% 19.41/2.98  --res_orphan_elimination                true
% 19.41/2.98  --res_time_limit                        2.
% 19.41/2.98  --res_out_proof                         true
% 19.41/2.98  
% 19.41/2.98  ------ Superposition Options
% 19.41/2.98  
% 19.41/2.98  --superposition_flag                    true
% 19.41/2.98  --sup_passive_queue_type                priority_queues
% 19.41/2.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.41/2.98  --sup_passive_queues_freq               [1;4]
% 19.41/2.98  --demod_completeness_check              fast
% 19.41/2.98  --demod_use_ground                      true
% 19.41/2.98  --sup_to_prop_solver                    passive
% 19.41/2.98  --sup_prop_simpl_new                    true
% 19.41/2.98  --sup_prop_simpl_given                  true
% 19.41/2.98  --sup_fun_splitting                     false
% 19.41/2.98  --sup_smt_interval                      50000
% 19.41/2.98  
% 19.41/2.98  ------ Superposition Simplification Setup
% 19.41/2.98  
% 19.41/2.98  --sup_indices_passive                   []
% 19.41/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.41/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_full_bw                           [BwDemod]
% 19.41/2.98  --sup_immed_triv                        [TrivRules]
% 19.41/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.41/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_immed_bw_main                     []
% 19.41/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.41/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.41/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.41/2.98  
% 19.41/2.98  ------ Combination Options
% 19.41/2.98  
% 19.41/2.98  --comb_res_mult                         3
% 19.41/2.98  --comb_sup_mult                         2
% 19.41/2.98  --comb_inst_mult                        10
% 19.41/2.98  
% 19.41/2.98  ------ Debug Options
% 19.41/2.98  
% 19.41/2.98  --dbg_backtrace                         false
% 19.41/2.98  --dbg_dump_prop_clauses                 false
% 19.41/2.98  --dbg_dump_prop_clauses_file            -
% 19.41/2.98  --dbg_out_stat                          false
% 19.41/2.98  ------ Parsing...
% 19.41/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.41/2.98  
% 19.41/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.41/2.98  
% 19.41/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.41/2.98  
% 19.41/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.41/2.98  ------ Proving...
% 19.41/2.98  ------ Problem Properties 
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  clauses                                 17
% 19.41/2.98  conjectures                             3
% 19.41/2.98  EPR                                     2
% 19.41/2.98  Horn                                    14
% 19.41/2.98  unary                                   4
% 19.41/2.98  binary                                  7
% 19.41/2.98  lits                                    36
% 19.41/2.98  lits eq                                 13
% 19.41/2.98  fd_pure                                 0
% 19.41/2.98  fd_pseudo                               0
% 19.41/2.98  fd_cond                                 1
% 19.41/2.98  fd_pseudo_cond                          4
% 19.41/2.98  AC symbols                              0
% 19.41/2.98  
% 19.41/2.98  ------ Input Options Time Limit: Unbounded
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  ------ 
% 19.41/2.98  Current options:
% 19.41/2.98  ------ 
% 19.41/2.98  
% 19.41/2.98  ------ Input Options
% 19.41/2.98  
% 19.41/2.98  --out_options                           all
% 19.41/2.98  --tptp_safe_out                         true
% 19.41/2.98  --problem_path                          ""
% 19.41/2.98  --include_path                          ""
% 19.41/2.98  --clausifier                            res/vclausify_rel
% 19.41/2.98  --clausifier_options                    --mode clausify
% 19.41/2.98  --stdin                                 false
% 19.41/2.98  --stats_out                             sel
% 19.41/2.98  
% 19.41/2.98  ------ General Options
% 19.41/2.98  
% 19.41/2.98  --fof                                   false
% 19.41/2.98  --time_out_real                         604.99
% 19.41/2.98  --time_out_virtual                      -1.
% 19.41/2.98  --symbol_type_check                     false
% 19.41/2.98  --clausify_out                          false
% 19.41/2.98  --sig_cnt_out                           false
% 19.41/2.98  --trig_cnt_out                          false
% 19.41/2.98  --trig_cnt_out_tolerance                1.
% 19.41/2.98  --trig_cnt_out_sk_spl                   false
% 19.41/2.98  --abstr_cl_out                          false
% 19.41/2.98  
% 19.41/2.98  ------ Global Options
% 19.41/2.98  
% 19.41/2.98  --schedule                              none
% 19.41/2.98  --add_important_lit                     false
% 19.41/2.98  --prop_solver_per_cl                    1000
% 19.41/2.98  --min_unsat_core                        false
% 19.41/2.98  --soft_assumptions                      false
% 19.41/2.98  --soft_lemma_size                       3
% 19.41/2.98  --prop_impl_unit_size                   0
% 19.41/2.98  --prop_impl_unit                        []
% 19.41/2.98  --share_sel_clauses                     true
% 19.41/2.98  --reset_solvers                         false
% 19.41/2.98  --bc_imp_inh                            [conj_cone]
% 19.41/2.98  --conj_cone_tolerance                   3.
% 19.41/2.98  --extra_neg_conj                        none
% 19.41/2.98  --large_theory_mode                     true
% 19.41/2.98  --prolific_symb_bound                   200
% 19.41/2.98  --lt_threshold                          2000
% 19.41/2.98  --clause_weak_htbl                      true
% 19.41/2.98  --gc_record_bc_elim                     false
% 19.41/2.98  
% 19.41/2.98  ------ Preprocessing Options
% 19.41/2.98  
% 19.41/2.98  --preprocessing_flag                    true
% 19.41/2.98  --time_out_prep_mult                    0.1
% 19.41/2.98  --splitting_mode                        input
% 19.41/2.98  --splitting_grd                         true
% 19.41/2.98  --splitting_cvd                         false
% 19.41/2.98  --splitting_cvd_svl                     false
% 19.41/2.98  --splitting_nvd                         32
% 19.41/2.98  --sub_typing                            true
% 19.41/2.98  --prep_gs_sim                           false
% 19.41/2.98  --prep_unflatten                        true
% 19.41/2.98  --prep_res_sim                          true
% 19.41/2.98  --prep_upred                            true
% 19.41/2.98  --prep_sem_filter                       exhaustive
% 19.41/2.98  --prep_sem_filter_out                   false
% 19.41/2.98  --pred_elim                             false
% 19.41/2.98  --res_sim_input                         true
% 19.41/2.98  --eq_ax_congr_red                       true
% 19.41/2.98  --pure_diseq_elim                       true
% 19.41/2.98  --brand_transform                       false
% 19.41/2.98  --non_eq_to_eq                          false
% 19.41/2.98  --prep_def_merge                        true
% 19.41/2.98  --prep_def_merge_prop_impl              false
% 19.41/2.98  --prep_def_merge_mbd                    true
% 19.41/2.98  --prep_def_merge_tr_red                 false
% 19.41/2.98  --prep_def_merge_tr_cl                  false
% 19.41/2.98  --smt_preprocessing                     true
% 19.41/2.98  --smt_ac_axioms                         fast
% 19.41/2.98  --preprocessed_out                      false
% 19.41/2.98  --preprocessed_stats                    false
% 19.41/2.98  
% 19.41/2.98  ------ Abstraction refinement Options
% 19.41/2.98  
% 19.41/2.98  --abstr_ref                             []
% 19.41/2.98  --abstr_ref_prep                        false
% 19.41/2.98  --abstr_ref_until_sat                   false
% 19.41/2.98  --abstr_ref_sig_restrict                funpre
% 19.41/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.41/2.98  --abstr_ref_under                       []
% 19.41/2.98  
% 19.41/2.98  ------ SAT Options
% 19.41/2.98  
% 19.41/2.98  --sat_mode                              false
% 19.41/2.98  --sat_fm_restart_options                ""
% 19.41/2.98  --sat_gr_def                            false
% 19.41/2.98  --sat_epr_types                         true
% 19.41/2.98  --sat_non_cyclic_types                  false
% 19.41/2.98  --sat_finite_models                     false
% 19.41/2.98  --sat_fm_lemmas                         false
% 19.41/2.98  --sat_fm_prep                           false
% 19.41/2.98  --sat_fm_uc_incr                        true
% 19.41/2.98  --sat_out_model                         small
% 19.41/2.98  --sat_out_clauses                       false
% 19.41/2.98  
% 19.41/2.98  ------ QBF Options
% 19.41/2.98  
% 19.41/2.98  --qbf_mode                              false
% 19.41/2.98  --qbf_elim_univ                         false
% 19.41/2.98  --qbf_dom_inst                          none
% 19.41/2.98  --qbf_dom_pre_inst                      false
% 19.41/2.98  --qbf_sk_in                             false
% 19.41/2.98  --qbf_pred_elim                         true
% 19.41/2.98  --qbf_split                             512
% 19.41/2.98  
% 19.41/2.98  ------ BMC1 Options
% 19.41/2.98  
% 19.41/2.98  --bmc1_incremental                      false
% 19.41/2.98  --bmc1_axioms                           reachable_all
% 19.41/2.98  --bmc1_min_bound                        0
% 19.41/2.98  --bmc1_max_bound                        -1
% 19.41/2.98  --bmc1_max_bound_default                -1
% 19.41/2.98  --bmc1_symbol_reachability              true
% 19.41/2.98  --bmc1_property_lemmas                  false
% 19.41/2.98  --bmc1_k_induction                      false
% 19.41/2.98  --bmc1_non_equiv_states                 false
% 19.41/2.98  --bmc1_deadlock                         false
% 19.41/2.98  --bmc1_ucm                              false
% 19.41/2.98  --bmc1_add_unsat_core                   none
% 19.41/2.98  --bmc1_unsat_core_children              false
% 19.41/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.41/2.98  --bmc1_out_stat                         full
% 19.41/2.98  --bmc1_ground_init                      false
% 19.41/2.98  --bmc1_pre_inst_next_state              false
% 19.41/2.98  --bmc1_pre_inst_state                   false
% 19.41/2.98  --bmc1_pre_inst_reach_state             false
% 19.41/2.98  --bmc1_out_unsat_core                   false
% 19.41/2.98  --bmc1_aig_witness_out                  false
% 19.41/2.98  --bmc1_verbose                          false
% 19.41/2.98  --bmc1_dump_clauses_tptp                false
% 19.41/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.41/2.98  --bmc1_dump_file                        -
% 19.41/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.41/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.41/2.98  --bmc1_ucm_extend_mode                  1
% 19.41/2.98  --bmc1_ucm_init_mode                    2
% 19.41/2.98  --bmc1_ucm_cone_mode                    none
% 19.41/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.41/2.98  --bmc1_ucm_relax_model                  4
% 19.41/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.41/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.41/2.98  --bmc1_ucm_layered_model                none
% 19.41/2.98  --bmc1_ucm_max_lemma_size               10
% 19.41/2.98  
% 19.41/2.98  ------ AIG Options
% 19.41/2.98  
% 19.41/2.98  --aig_mode                              false
% 19.41/2.98  
% 19.41/2.98  ------ Instantiation Options
% 19.41/2.98  
% 19.41/2.98  --instantiation_flag                    true
% 19.41/2.98  --inst_sos_flag                         false
% 19.41/2.98  --inst_sos_phase                        true
% 19.41/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.41/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.41/2.98  --inst_lit_sel_side                     num_symb
% 19.41/2.98  --inst_solver_per_active                1400
% 19.41/2.98  --inst_solver_calls_frac                1.
% 19.41/2.98  --inst_passive_queue_type               priority_queues
% 19.41/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.41/2.98  --inst_passive_queues_freq              [25;2]
% 19.41/2.98  --inst_dismatching                      true
% 19.41/2.98  --inst_eager_unprocessed_to_passive     true
% 19.41/2.98  --inst_prop_sim_given                   true
% 19.41/2.98  --inst_prop_sim_new                     false
% 19.41/2.98  --inst_subs_new                         false
% 19.41/2.98  --inst_eq_res_simp                      false
% 19.41/2.98  --inst_subs_given                       false
% 19.41/2.98  --inst_orphan_elimination               true
% 19.41/2.98  --inst_learning_loop_flag               true
% 19.41/2.98  --inst_learning_start                   3000
% 19.41/2.98  --inst_learning_factor                  2
% 19.41/2.98  --inst_start_prop_sim_after_learn       3
% 19.41/2.98  --inst_sel_renew                        solver
% 19.41/2.98  --inst_lit_activity_flag                true
% 19.41/2.98  --inst_restr_to_given                   false
% 19.41/2.98  --inst_activity_threshold               500
% 19.41/2.98  --inst_out_proof                        true
% 19.41/2.98  
% 19.41/2.98  ------ Resolution Options
% 19.41/2.98  
% 19.41/2.98  --resolution_flag                       true
% 19.41/2.98  --res_lit_sel                           adaptive
% 19.41/2.98  --res_lit_sel_side                      none
% 19.41/2.98  --res_ordering                          kbo
% 19.41/2.98  --res_to_prop_solver                    active
% 19.41/2.98  --res_prop_simpl_new                    false
% 19.41/2.98  --res_prop_simpl_given                  true
% 19.41/2.98  --res_passive_queue_type                priority_queues
% 19.41/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.41/2.98  --res_passive_queues_freq               [15;5]
% 19.41/2.98  --res_forward_subs                      full
% 19.41/2.98  --res_backward_subs                     full
% 19.41/2.98  --res_forward_subs_resolution           true
% 19.41/2.98  --res_backward_subs_resolution          true
% 19.41/2.98  --res_orphan_elimination                true
% 19.41/2.98  --res_time_limit                        2.
% 19.41/2.98  --res_out_proof                         true
% 19.41/2.98  
% 19.41/2.98  ------ Superposition Options
% 19.41/2.98  
% 19.41/2.98  --superposition_flag                    true
% 19.41/2.98  --sup_passive_queue_type                priority_queues
% 19.41/2.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.41/2.98  --sup_passive_queues_freq               [1;4]
% 19.41/2.98  --demod_completeness_check              fast
% 19.41/2.98  --demod_use_ground                      true
% 19.41/2.98  --sup_to_prop_solver                    passive
% 19.41/2.98  --sup_prop_simpl_new                    true
% 19.41/2.98  --sup_prop_simpl_given                  true
% 19.41/2.98  --sup_fun_splitting                     false
% 19.41/2.98  --sup_smt_interval                      50000
% 19.41/2.98  
% 19.41/2.98  ------ Superposition Simplification Setup
% 19.41/2.98  
% 19.41/2.98  --sup_indices_passive                   []
% 19.41/2.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.41/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.41/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_full_bw                           [BwDemod]
% 19.41/2.98  --sup_immed_triv                        [TrivRules]
% 19.41/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.41/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_immed_bw_main                     []
% 19.41/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.41/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.41/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.41/2.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.41/2.98  
% 19.41/2.98  ------ Combination Options
% 19.41/2.98  
% 19.41/2.98  --comb_res_mult                         3
% 19.41/2.98  --comb_sup_mult                         2
% 19.41/2.98  --comb_inst_mult                        10
% 19.41/2.98  
% 19.41/2.98  ------ Debug Options
% 19.41/2.98  
% 19.41/2.98  --dbg_backtrace                         false
% 19.41/2.98  --dbg_dump_prop_clauses                 false
% 19.41/2.98  --dbg_dump_prop_clauses_file            -
% 19.41/2.98  --dbg_out_stat                          false
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  ------ Proving...
% 19.41/2.98  
% 19.41/2.98  
% 19.41/2.98  % SZS status Theorem for theBenchmark.p
% 19.41/2.98  
% 19.41/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.41/2.98  
% 19.41/2.98  fof(f1,axiom,(
% 19.41/2.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 19.41/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.41/2.98  
% 19.41/2.98  fof(f8,plain,(
% 19.41/2.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 19.41/2.98    inference(nnf_transformation,[],[f1])).
% 19.41/2.98  
% 19.41/2.98  fof(f9,plain,(
% 19.41/2.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 19.41/2.98    inference(flattening,[],[f8])).
% 19.41/2.98  
% 19.41/2.98  fof(f28,plain,(
% 19.41/2.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 19.41/2.98    inference(cnf_transformation,[],[f9])).
% 19.41/2.98  
% 19.41/2.98  fof(f3,axiom,(
% 19.41/2.98    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 19.41/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.41/2.98  
% 19.41/2.98  fof(f12,plain,(
% 19.41/2.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 19.41/2.98    inference(nnf_transformation,[],[f3])).
% 19.41/2.98  
% 19.41/2.98  fof(f13,plain,(
% 19.41/2.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 19.41/2.98    inference(rectify,[],[f12])).
% 19.41/2.98  
% 19.41/2.98  fof(f16,plain,(
% 19.41/2.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f15,plain,(
% 19.41/2.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f14,plain,(
% 19.41/2.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f17,plain,(
% 19.41/2.98    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 19.41/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).
% 19.41/2.98  
% 19.41/2.98  fof(f33,plain,(
% 19.41/2.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 19.41/2.98    inference(cnf_transformation,[],[f17])).
% 19.41/2.98  
% 19.41/2.98  fof(f45,plain,(
% 19.41/2.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 19.41/2.98    inference(equality_resolution,[],[f33])).
% 19.41/2.98  
% 19.41/2.98  fof(f32,plain,(
% 19.41/2.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 19.41/2.98    inference(cnf_transformation,[],[f17])).
% 19.41/2.98  
% 19.41/2.98  fof(f46,plain,(
% 19.41/2.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 19.41/2.98    inference(equality_resolution,[],[f32])).
% 19.41/2.98  
% 19.41/2.98  fof(f4,axiom,(
% 19.41/2.98    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 19.41/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.41/2.98  
% 19.41/2.98  fof(f18,plain,(
% 19.41/2.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 19.41/2.98    inference(nnf_transformation,[],[f4])).
% 19.41/2.98  
% 19.41/2.98  fof(f19,plain,(
% 19.41/2.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.41/2.98    inference(rectify,[],[f18])).
% 19.41/2.98  
% 19.41/2.98  fof(f22,plain,(
% 19.41/2.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f21,plain,(
% 19.41/2.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f20,plain,(
% 19.41/2.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f23,plain,(
% 19.41/2.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.41/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).
% 19.41/2.98  
% 19.41/2.98  fof(f38,plain,(
% 19.41/2.98    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 19.41/2.98    inference(cnf_transformation,[],[f23])).
% 19.41/2.98  
% 19.41/2.98  fof(f27,plain,(
% 19.41/2.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 19.41/2.98    inference(cnf_transformation,[],[f9])).
% 19.41/2.98  
% 19.41/2.98  fof(f5,conjecture,(
% 19.41/2.98    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 19.41/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.41/2.98  
% 19.41/2.98  fof(f6,negated_conjecture,(
% 19.41/2.98    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 19.41/2.98    inference(negated_conjecture,[],[f5])).
% 19.41/2.98  
% 19.41/2.98  fof(f7,plain,(
% 19.41/2.98    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 19.41/2.98    inference(ennf_transformation,[],[f6])).
% 19.41/2.98  
% 19.41/2.98  fof(f24,plain,(
% 19.41/2.98    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7 | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6)),
% 19.41/2.98    introduced(choice_axiom,[])).
% 19.41/2.98  
% 19.41/2.98  fof(f25,plain,(
% 19.41/2.98    (k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7 | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6) & k1_xboole_0 != sK7 & k1_xboole_0 != sK6),
% 19.41/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f7,f24])).
% 19.41/2.98  
% 19.41/2.98  fof(f42,plain,(
% 19.41/2.98    k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7 | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6),
% 19.41/2.98    inference(cnf_transformation,[],[f25])).
% 19.41/2.98  
% 19.41/2.98  fof(f26,plain,(
% 19.41/2.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 19.41/2.98    inference(cnf_transformation,[],[f9])).
% 19.41/2.98  
% 19.41/2.98  fof(f34,plain,(
% 19.41/2.98    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 19.41/2.98    inference(cnf_transformation,[],[f17])).
% 19.41/2.98  
% 19.41/2.98  fof(f40,plain,(
% 19.41/2.98    k1_xboole_0 != sK6),
% 19.41/2.98    inference(cnf_transformation,[],[f25])).
% 19.41/2.98  
% 19.41/2.98  fof(f2,axiom,(
% 19.41/2.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.41/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.41/2.98  
% 19.41/2.98  fof(f10,plain,(
% 19.41/2.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 19.41/2.98    inference(nnf_transformation,[],[f2])).
% 19.41/2.98  
% 19.41/2.98  fof(f11,plain,(
% 19.41/2.98    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 19.41/2.98    inference(flattening,[],[f10])).
% 19.41/2.98  
% 19.41/2.98  fof(f29,plain,(
% 19.41/2.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 19.41/2.98    inference(cnf_transformation,[],[f11])).
% 19.41/2.98  
% 19.41/2.98  fof(f30,plain,(
% 19.41/2.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 19.41/2.98    inference(cnf_transformation,[],[f11])).
% 19.41/2.98  
% 19.41/2.98  fof(f44,plain,(
% 19.41/2.98    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 19.41/2.98    inference(equality_resolution,[],[f30])).
% 19.41/2.98  
% 19.41/2.98  fof(f31,plain,(
% 19.41/2.98    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 19.41/2.98    inference(cnf_transformation,[],[f11])).
% 19.41/2.98  
% 19.41/2.98  fof(f43,plain,(
% 19.41/2.98    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.41/2.98    inference(equality_resolution,[],[f31])).
% 19.41/2.98  
% 19.41/2.98  fof(f35,plain,(
% 19.41/2.98    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.41/2.98    inference(cnf_transformation,[],[f17])).
% 19.41/2.98  
% 19.41/2.98  fof(f39,plain,(
% 19.41/2.98    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 19.41/2.98    inference(cnf_transformation,[],[f23])).
% 19.41/2.98  
% 19.41/2.98  fof(f36,plain,(
% 19.41/2.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 19.41/2.98    inference(cnf_transformation,[],[f23])).
% 19.41/2.98  
% 19.41/2.98  fof(f48,plain,(
% 19.41/2.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 19.41/2.98    inference(equality_resolution,[],[f36])).
% 19.41/2.98  
% 19.41/2.98  fof(f37,plain,(
% 19.41/2.98    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 19.41/2.98    inference(cnf_transformation,[],[f23])).
% 19.41/2.98  
% 19.41/2.98  fof(f47,plain,(
% 19.41/2.98    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 19.41/2.98    inference(equality_resolution,[],[f37])).
% 19.41/2.98  
% 19.41/2.98  fof(f41,plain,(
% 19.41/2.98    k1_xboole_0 != sK7),
% 19.41/2.98    inference(cnf_transformation,[],[f25])).
% 19.41/2.98  
% 19.41/2.98  cnf(c_0,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(X2,X3)
% 19.41/2.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 19.41/2.98      inference(cnf_transformation,[],[f28]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_8,plain,
% 19.41/2.98      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 19.41/2.98      inference(cnf_transformation,[],[f45]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_2725,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(X2,X3)
% 19.41/2.98      | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,X1))) ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_0,c_8]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_9,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.41/2.98      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
% 19.41/2.98      inference(cnf_transformation,[],[f46]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_3622,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(X2,k1_relat_1(X3))
% 19.41/2.98      | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,X3))) ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_2725,c_9]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_11,plain,
% 19.41/2.98      ( r2_hidden(sK3(X0,X1),X1)
% 19.41/2.98      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
% 19.41/2.98      | k2_relat_1(X0) = X1 ),
% 19.41/2.98      inference(cnf_transformation,[],[f38]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_1,plain,
% 19.41/2.98      ( r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 19.41/2.98      inference(cnf_transformation,[],[f27]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_3075,plain,
% 19.41/2.98      ( r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X2)
% 19.41/2.98      | r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X1)
% 19.41/2.98      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X2 ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_11,c_1]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_14,negated_conjecture,
% 19.41/2.98      ( k2_relat_1(k2_zfmisc_1(sK6,sK7)) != sK7
% 19.41/2.98      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
% 19.41/2.98      inference(cnf_transformation,[],[f42]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_11778,plain,
% 19.41/2.98      ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.98      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_3075,c_14]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_2,plain,
% 19.41/2.98      ( r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 19.41/2.98      inference(cnf_transformation,[],[f26]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_7,plain,
% 19.41/2.98      ( r2_hidden(sK0(X0,X1),X1)
% 19.41/2.98      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 19.41/2.98      | k1_relat_1(X0) = X1 ),
% 19.41/2.98      inference(cnf_transformation,[],[f34]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_1888,plain,
% 19.41/2.98      ( r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2)
% 19.41/2.98      | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X0)
% 19.41/2.98      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X2 ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_2,c_7]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_12523,plain,
% 19.41/2.98      ( r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_11778,c_1888]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_13180,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,X1)
% 19.41/2.98      | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,sK7)))
% 19.41/2.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_12523,c_2725]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_24860,plain,
% 19.41/2.98      ( ~ r2_hidden(X0,X1)
% 19.41/2.98      | ~ r2_hidden(X2,X3)
% 19.41/2.98      | r2_hidden(X0,k1_relat_1(k2_zfmisc_1(X1,k2_zfmisc_1(X3,sK7))))
% 19.41/2.98      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.98      inference(resolution,[status(thm)],[c_3622,c_13180]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_16,negated_conjecture,
% 19.41/2.98      ( k1_xboole_0 != sK6 ),
% 19.41/2.98      inference(cnf_transformation,[],[f40]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_5,plain,
% 19.41/2.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 19.41/2.98      | k1_xboole_0 = X1
% 19.41/2.98      | k1_xboole_0 = X0 ),
% 19.41/2.98      inference(cnf_transformation,[],[f29]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_41,plain,
% 19.41/2.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.41/2.98      | k1_xboole_0 = k1_xboole_0 ),
% 19.41/2.98      inference(instantiation,[status(thm)],[c_5]) ).
% 19.41/2.98  
% 19.41/2.98  cnf(c_4,plain,
% 19.41/2.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.41/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_42,plain,
% 19.41/2.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_120,plain,( X0 = X0 ),theory(equality) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_557,plain,
% 19.41/2.99      ( sK6 = sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_120]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_121,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_462,plain,
% 19.41/2.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_665,plain,
% 19.41/2.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_462]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1088,plain,
% 19.41/2.99      ( k1_relat_1(X0) != sK6 | sK6 = k1_relat_1(X0) | sK6 != sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_665]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1089,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) != sK6
% 19.41/2.99      | sK6 = k1_relat_1(k1_xboole_0)
% 19.41/2.99      | sK6 != sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_1088]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_307,plain,
% 19.41/2.99      ( k1_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) = iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_3,plain,
% 19.41/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_309,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_739,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_3,c_309]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1330,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X1) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_307,c_739]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1402,plain,
% 19.41/2.99      ( r2_hidden(sK0(k1_xboole_0,X0),X0)
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X1)
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = X0 ),
% 19.41/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_1330]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1404,plain,
% 19.41/2.99      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_305,plain,
% 19.41/2.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_6,plain,
% 19.41/2.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 19.41/2.99      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
% 19.41/2.99      | k1_relat_1(X0) = X1 ),
% 19.41/2.99      inference(cnf_transformation,[],[f35]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_308,plain,
% 19.41/2.99      ( k1_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK0(X0,X1),X2),X0) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1447,plain,
% 19.41/2.99      ( k1_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_305,c_308]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1465,plain,
% 19.41/2.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 19.41/2.99      | ~ r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 19.41/2.99      | k1_relat_1(X0) = X1 ),
% 19.41/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_1447]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1467,plain,
% 19.41/2.99      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 19.41/2.99      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_1465]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2096,plain,
% 19.41/2.99      ( k1_relat_1(X0) != X1
% 19.41/2.99      | k1_xboole_0 != X1
% 19.41/2.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2097,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 19.41/2.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_2096]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_10,plain,
% 19.41/2.99      ( ~ r2_hidden(sK3(X0,X1),X1)
% 19.41/2.99      | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
% 19.41/2.99      | k2_relat_1(X0) = X1 ),
% 19.41/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_4968,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1)
% 19.41/2.99      | ~ r2_hidden(sK3(k2_zfmisc_1(X1,X2),X3),X3)
% 19.41/2.99      | ~ r2_hidden(sK3(k2_zfmisc_1(X1,X2),X3),X2)
% 19.41/2.99      | k2_relat_1(k2_zfmisc_1(X1,X2)) = X3 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_10,c_0]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_16202,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,sK6)
% 19.41/2.99      | ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_4968,c_12523]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_443,plain,
% 19.41/2.99      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK1(k2_zfmisc_1(sK6,sK7),sK6)),k2_zfmisc_1(sK6,sK7))
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_7]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1036,plain,
% 19.41/2.99      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK1(k2_zfmisc_1(sK6,sK7),sK6)),k2_zfmisc_1(sK6,sK7)) ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_2]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_17023,plain,
% 19.41/2.99      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | ~ r2_hidden(X0,sK6) ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_16202,c_14,c_443,c_1036,c_12523]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_17024,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,sK6)
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.99      inference(renaming,[status(thm)],[c_17023]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1757,plain,
% 19.41/2.99      ( r2_hidden(sK0(X0,X1),X1)
% 19.41/2.99      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 19.41/2.99      | k1_relat_1(X0) = X1 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_17041,plain,
% 19.41/2.99      ( r2_hidden(sK0(X0,sK6),k1_relat_1(X0))
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | k1_relat_1(X0) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_17024,c_1757]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_124,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.41/2.99      theory(equality) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2742,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
% 19.41/2.99      | ~ r2_hidden(X2,k1_xboole_0)
% 19.41/2.99      | X0 != X2 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_124,c_4]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_4989,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))
% 19.41/2.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_2742,c_120]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_5490,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k1_xboole_0) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_4989,c_1]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_5520,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 19.41/2.99      | r2_hidden(sK2(k1_xboole_0,X0),X1) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_5490,c_9]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_17103,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_17024,c_5520]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_21575,plain,
% 19.41/2.99      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_17041,c_17103]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_306,plain,
% 19.41/2.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1328,plain,
% 19.41/2.99      ( k1_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_307,c_306]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_311,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.41/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1445,plain,
% 19.41/2.99      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X2
% 19.41/2.99      | r2_hidden(X3,X1) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X0) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(X0,X1),X2),X2) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_311,c_308]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_25944,plain,
% 19.41/2.99      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = X1
% 19.41/2.99      | r2_hidden(X2,X0) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(k1_xboole_0,X0),X1),k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X1),X1) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_4,c_1445]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_25949,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(X1,X2) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(light_normalisation,[status(thm)],[c_25944,c_4]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_5178,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top
% 19.41/2.99      | iProver_top != iProver_top ),
% 19.41/2.99      inference(equality_factoring,[status(thm)],[c_1330]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_5180,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 19.41/2.99      inference(equality_resolution_simp,[status(thm)],[c_5178]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_26280,plain,
% 19.41/2.99      ( r2_hidden(X1,X2) != iProver_top
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_25949,c_5180]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_26281,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(X1,X2) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(renaming,[status(thm)],[c_26280]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_26288,plain,
% 19.41/2.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 19.41/2.99      | r2_hidden(X0,X1) != iProver_top
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_1328,c_26281]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_26304,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1)
% 19.41/2.99      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
% 19.41/2.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_26288]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_431,plain,
% 19.41/2.99      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_27990,plain,
% 19.41/2.99      ( sK6 != k1_relat_1(X0)
% 19.41/2.99      | k1_xboole_0 != k1_relat_1(X0)
% 19.41/2.99      | k1_xboole_0 = sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_431]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_27991,plain,
% 19.41/2.99      ( sK6 != k1_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 = sK6 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_27990]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_31796,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1)
% 19.41/2.99      | r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_24860,c_16,c_41,c_42,c_557,c_1089,c_1404,c_1467,
% 19.41/2.99                 c_2097,c_21575,c_26304,c_27991]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_32558,plain,
% 19.41/2.99      ( r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6) ),
% 19.41/2.99      inference(backward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_31796,c_12523]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_4952,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1)
% 19.41/2.99      | ~ r2_hidden(sK0(k2_zfmisc_1(X2,X1),X3),X3)
% 19.41/2.99      | ~ r2_hidden(sK0(k2_zfmisc_1(X2,X1),X3),X2)
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(X2,X1)) = X3 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_6,c_0]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_32847,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,sK7)
% 19.41/2.99      | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_32558,c_4952]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_33308,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,sK7) | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_32847,c_32558]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_11864,plain,
% 19.41/2.99      ( r2_hidden(sK3(k2_zfmisc_1(X0,X1),X1),X1)
% 19.41/2.99      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ),
% 19.41/2.99      inference(factoring,[status(thm)],[c_3075]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_33413,plain,
% 19.41/2.99      ( k2_relat_1(k2_zfmisc_1(X0,sK7)) = sK7
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_33308,c_11864]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_449,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,X1)
% 19.41/2.99      | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),X0),k2_zfmisc_1(sK6,X1)) ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_0]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1665,plain,
% 19.41/2.99      ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.99      | ~ r2_hidden(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK6)
% 19.41/2.99      | r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7)) ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_449]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_492,plain,
% 19.41/2.99      ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.99      | ~ r2_hidden(k4_tarski(X0,sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7))
% 19.41/2.99      | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_10]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_41651,plain,
% 19.41/2.99      ( ~ r2_hidden(sK3(k2_zfmisc_1(sK6,sK7),sK7),sK7)
% 19.41/2.99      | ~ r2_hidden(k4_tarski(sK0(k2_zfmisc_1(sK6,sK7),sK6),sK3(k2_zfmisc_1(sK6,sK7),sK7)),k2_zfmisc_1(sK6,sK7))
% 19.41/2.99      | k2_relat_1(k2_zfmisc_1(sK6,sK7)) = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_492]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_58942,plain,
% 19.41/2.99      ( k2_relat_1(k2_zfmisc_1(X0,sK7)) = sK7 ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_33413,c_14,c_1665,c_11778,c_32558,c_41651]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_58949,plain,
% 19.41/2.99      ( k1_relat_1(k2_zfmisc_1(sK6,sK7)) != sK6 ),
% 19.41/2.99      inference(backward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_58942,c_14]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2738,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 19.41/2.99      | ~ r2_hidden(X2,k1_xboole_0)
% 19.41/2.99      | X0 != X2 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_124,c_3]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_3977,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 19.41/2.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_2738,c_120]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_4027,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k1_xboole_0) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_3977,c_2]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_13,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.41/2.99      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
% 19.41/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_4528,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
% 19.41/2.99      | r2_hidden(sK5(k1_xboole_0,X0),X1) ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_4027,c_13]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_33374,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_33308,c_4528]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_12,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 19.41/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_3081,plain,
% 19.41/2.99      ( r2_hidden(sK3(X0,X1),X1)
% 19.41/2.99      | r2_hidden(sK3(X0,X1),k2_relat_1(X0))
% 19.41/2.99      | k2_relat_1(X0) = X1 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_11,c_12]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_40647,plain,
% 19.41/2.99      ( r2_hidden(sK3(k1_xboole_0,X0),X0)
% 19.41/2.99      | k2_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_33374,c_3081]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_59900,plain,
% 19.41/2.99      ( r2_hidden(sK3(k1_xboole_0,X0),X0)
% 19.41/2.99      | k2_relat_1(k1_xboole_0) = X0 ),
% 19.41/2.99      inference(backward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_58949,c_40647]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_59791,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,sK7) ),
% 19.41/2.99      inference(backward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_58949,c_33308]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_91456,plain,
% 19.41/2.99      ( k2_relat_1(k1_xboole_0) = sK7 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_59900,c_59791]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_303,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) = iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_737,plain,
% 19.41/2.99      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X2
% 19.41/2.99      | r2_hidden(sK4(k2_zfmisc_1(X0,X1),X2),X0) = iProver_top
% 19.41/2.99      | r2_hidden(sK3(k2_zfmisc_1(X0,X1),X2),X2) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_303,c_309]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_3161,plain,
% 19.41/2.99      ( k2_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = X1
% 19.41/2.99      | r2_hidden(sK4(k1_xboole_0,X1),k1_xboole_0) = iProver_top
% 19.41/2.99      | r2_hidden(sK3(k2_zfmisc_1(k1_xboole_0,X0),X1),X1) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_4,c_737]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_3285,plain,
% 19.41/2.99      ( k2_relat_1(k1_xboole_0) = X0
% 19.41/2.99      | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 19.41/2.99      | r2_hidden(sK3(k1_xboole_0,X0),X0) = iProver_top ),
% 19.41/2.99      inference(light_normalisation,[status(thm)],[c_3161,c_4]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_614,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_303,c_306]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1110,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_3,c_311]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1941,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_614,c_1110]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_301,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_304,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_946,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) != iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_301,c_304]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_302,plain,
% 19.41/2.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_615,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_303,c_302]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2423,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_615,c_1110]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2427,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_615,c_1110]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57735,plain,
% 19.41/2.99      ( r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_1941,c_946,c_2423,c_2427]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57736,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(sK3(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(renaming,[status(thm)],[c_57735]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1111,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_4,c_311]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1940,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_614,c_1111]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2422,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_615,c_1111]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2426,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(sK3(X0,X1),k2_relat_1(X0)) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_615,c_1111]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_55607,plain,
% 19.41/2.99      ( r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_1940,c_946,c_2422,c_2426]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_55608,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,sK3(X0,X1)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(renaming,[status(thm)],[c_55607]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1114,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.41/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.41/2.99      | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,X1))) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_311,c_306]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_55618,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.41/2.99      | r2_hidden(X2,k1_relat_1(k2_zfmisc_1(X3,k1_xboole_0))) = iProver_top
% 19.41/2.99      | r2_hidden(X4,k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_55608,c_1114]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_55718,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.41/2.99      | r2_hidden(X2,k1_relat_1(k1_xboole_0)) = iProver_top
% 19.41/2.99      | r2_hidden(X4,k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(demodulation,[status(thm)],[c_55618,c_3]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_310,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_866,plain,
% 19.41/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_4,c_310]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_964,plain,
% 19.41/2.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 19.41/2.99      | r2_hidden(sK2(k1_xboole_0,X0),X1) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_305,c_866]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1854,plain,
% 19.41/2.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 19.41/2.99      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 19.41/2.99      | r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_964,c_1111]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_33386,plain,
% 19.41/2.99      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 19.41/2.99      | k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6 ),
% 19.41/2.99      inference(resolution,[status(thm)],[c_33308,c_5520]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_33387,plain,
% 19.41/2.99      ( k1_relat_1(k2_zfmisc_1(sK6,sK7)) = sK6
% 19.41/2.99      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 19.41/2.99      inference(predicate_to_equality,[status(thm)],[c_33386]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_51269,plain,
% 19.41/2.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 19.41/2.99      inference(global_propositional_subsumption,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_1854,c_14,c_1665,c_11778,c_32558,c_33387,c_41651]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57047,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | r2_hidden(X2,X3) != iProver_top
% 19.41/2.99      | r2_hidden(X4,k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(forward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_55718,c_51269]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57742,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1 | r2_hidden(X2,k1_xboole_0) != iProver_top ),
% 19.41/2.99      inference(forward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_57736,c_57047]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57757,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1
% 19.41/2.99      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 19.41/2.99      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 19.41/2.99      inference(superposition,[status(thm)],[c_3285,c_57742]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_57945,plain,
% 19.41/2.99      ( k2_relat_1(X0) = X1 | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(forward_subsumption_resolution,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_57757,c_57742]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_58760,plain,
% 19.41/2.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_57945]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_22802,plain,
% 19.41/2.99      ( k2_relat_1(X0) != X1
% 19.41/2.99      | k1_xboole_0 != X1
% 19.41/2.99      | k1_xboole_0 = k2_relat_1(X0) ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_22803,plain,
% 19.41/2.99      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 19.41/2.99      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_22802]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_429,plain,
% 19.41/2.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2340,plain,
% 19.41/2.99      ( sK7 != k2_relat_1(X0)
% 19.41/2.99      | k1_xboole_0 != k2_relat_1(X0)
% 19.41/2.99      | k1_xboole_0 = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_429]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_2341,plain,
% 19.41/2.99      ( sK7 != k2_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 != k2_relat_1(k1_xboole_0)
% 19.41/2.99      | k1_xboole_0 = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_2340]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_460,plain,
% 19.41/2.99      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_121]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_600,plain,
% 19.41/2.99      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_460]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1056,plain,
% 19.41/2.99      ( k2_relat_1(X0) != sK7 | sK7 = k2_relat_1(X0) | sK7 != sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_600]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_1059,plain,
% 19.41/2.99      ( k2_relat_1(k1_xboole_0) != sK7
% 19.41/2.99      | sK7 = k2_relat_1(k1_xboole_0)
% 19.41/2.99      | sK7 != sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_1056]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_601,plain,
% 19.41/2.99      ( sK7 = sK7 ),
% 19.41/2.99      inference(instantiation,[status(thm)],[c_120]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(c_15,negated_conjecture,
% 19.41/2.99      ( k1_xboole_0 != sK7 ),
% 19.41/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.41/2.99  
% 19.41/2.99  cnf(contradiction,plain,
% 19.41/2.99      ( $false ),
% 19.41/2.99      inference(minisat,
% 19.41/2.99                [status(thm)],
% 19.41/2.99                [c_91456,c_58760,c_22803,c_2341,c_1059,c_601,c_42,c_41,
% 19.41/2.99                 c_15]) ).
% 19.41/2.99  
% 19.41/2.99  
% 19.41/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.41/2.99  
% 19.41/2.99  ------                               Statistics
% 19.41/2.99  
% 19.41/2.99  ------ Selected
% 19.41/2.99  
% 19.41/2.99  total_time:                             2.309
% 19.41/2.99  
%------------------------------------------------------------------------------
