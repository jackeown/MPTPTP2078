%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:19 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 192 expanded)
%              Number of clauses        :   58 (  67 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 ( 841 expanded)
%              Number of equality atoms :  122 ( 205 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f21,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f21,f20])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( v1_relat_1(X0)
      | k4_tarski(X2,X3) != sK1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK2(X4),sK3(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK4(X0) != sK5(X0)
        & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK4(X0) != sK5(X0)
            & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).

fof(f39,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | sK4(X0) != sK5(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK7,sK6))
      & v4_relat_2(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v4_relat_2(k2_wellord1(sK7,sK6))
    & v4_relat_2(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f12,f27])).

fof(f45,plain,(
    ~ v4_relat_2(k2_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    v4_relat_2(sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15543,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15544,plain,
    ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15543])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | k4_tarski(X1,X2) != sK1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13605,plain,
    ( v1_relat_1(k2_wellord1(sK7,sK6))
    | k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) != sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13606,plain,
    ( k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) != sK1(k2_wellord1(sK7,sK6))
    | v1_relat_1(k2_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13605])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8098,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7)
    | ~ v1_relat_1(sK7)
    | k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) = sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8099,plain,
    ( k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) = sK1(k2_wellord1(sK7,sK6))
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8098])).

cnf(c_4037,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4038,plain,
    ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4037])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3570,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),X0)
    | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3571,plain,
    ( sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),X0) != iProver_top
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),X0) != iProver_top
    | v4_relat_2(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3570])).

cnf(c_3573,plain,
    ( sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) != iProver_top
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) != iProver_top
    | v4_relat_2(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3571])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1162,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
    | X1 != k2_wellord1(sK7,sK6)
    | X0 != sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1896,plain,
    ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),X0)
    | ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
    | X0 != k2_wellord1(sK7,sK6)
    | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_3073,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
    | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_3074,plain,
    ( k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
    | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6))
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6)) != iProver_top
    | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3073])).

cnf(c_3046,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3047,plain,
    ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3046])).

cnf(c_569,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2666,plain,
    ( k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) = k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1281,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | X1 != k2_wellord1(sK7,sK6)
    | X0 != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1664,plain,
    ( r2_hidden(X0,k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | X0 != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2665,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_2667,plain,
    ( k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2665])).

cnf(c_1209,plain,
    ( sK1(X0) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1897,plain,
    ( sK1(k2_wellord1(sK7,sK6)) = sK1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_1779,plain,
    ( k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) = k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_1267,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | X1 != k2_wellord1(sK7,sK6)
    | X0 != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1548,plain,
    ( r2_hidden(X0,k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | X0 != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1778,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
    | k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1780,plain,
    ( k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1549,plain,
    ( ~ v1_relat_1(sK7)
    | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) = k2_wellord1(sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1121,plain,
    ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
    | v1_relat_1(k2_wellord1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1122,plain,
    ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_10,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK5(X0) != sK4(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(sK7,sK6)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_264,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(sK7,sK6) != X0
    | sK5(X0) != sK4(X0) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_265,plain,
    ( ~ v1_relat_1(k2_wellord1(sK7,sK6))
    | sK5(k2_wellord1(sK7,sK6)) != sK4(k2_wellord1(sK7,sK6)) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_266,plain,
    ( sK5(k2_wellord1(sK7,sK6)) != sK4(k2_wellord1(sK7,sK6))
    | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_254,plain,
    ( r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK7,sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_255,plain,
    ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | ~ v1_relat_1(k2_wellord1(sK7,sK6)) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_256,plain,
    ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_244,plain,
    ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK7,sK6) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_245,plain,
    ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
    | ~ v1_relat_1(k2_wellord1(sK7,sK6)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_246,plain,
    ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) = iProver_top
    | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_15,negated_conjecture,
    ( v4_relat_2(sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,plain,
    ( v4_relat_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15544,c_13606,c_8099,c_4038,c_3573,c_3074,c_3047,c_2666,c_2667,c_1897,c_1779,c_1780,c_1549,c_1122,c_266,c_256,c_246,c_18,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.92/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.99  
% 3.92/0.99  ------  iProver source info
% 3.92/0.99  
% 3.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.99  git: non_committed_changes: false
% 3.92/0.99  git: last_make_outside_of_git: false
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  ------ Parsing...
% 3.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  ------ Proving...
% 3.92/0.99  ------ Problem Properties 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  clauses                                 17
% 3.92/0.99  conjectures                             3
% 3.92/0.99  EPR                                     2
% 3.92/0.99  Horn                                    12
% 3.92/0.99  unary                                   3
% 3.92/0.99  binary                                  5
% 3.92/0.99  lits                                    43
% 3.92/0.99  lits eq                                 8
% 3.92/0.99  fd_pure                                 0
% 3.92/0.99  fd_pseudo                               0
% 3.92/0.99  fd_cond                                 0
% 3.92/0.99  fd_pseudo_cond                          4
% 3.92/0.99  AC symbols                              0
% 3.92/0.99  
% 3.92/0.99  ------ Input Options Time Limit: Unbounded
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  Current options:
% 3.92/0.99  ------ 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  % SZS status Theorem for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  fof(f1,axiom,(
% 3.92/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f13,plain,(
% 3.92/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.92/0.99    inference(nnf_transformation,[],[f1])).
% 3.92/0.99  
% 3.92/0.99  fof(f14,plain,(
% 3.92/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.92/0.99    inference(flattening,[],[f13])).
% 3.92/0.99  
% 3.92/0.99  fof(f15,plain,(
% 3.92/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.92/0.99    inference(rectify,[],[f14])).
% 3.92/0.99  
% 3.92/0.99  fof(f16,plain,(
% 3.92/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f17,plain,(
% 3.92/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.92/0.99  
% 3.92/0.99  fof(f29,plain,(
% 3.92/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.92/0.99    inference(cnf_transformation,[],[f17])).
% 3.92/0.99  
% 3.92/0.99  fof(f48,plain,(
% 3.92/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.92/0.99    inference(equality_resolution,[],[f29])).
% 3.92/0.99  
% 3.92/0.99  fof(f2,axiom,(
% 3.92/0.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f7,plain,(
% 3.92/0.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 3.92/0.99    inference(ennf_transformation,[],[f2])).
% 3.92/0.99  
% 3.92/0.99  fof(f18,plain,(
% 3.92/0.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 3.92/0.99    inference(nnf_transformation,[],[f7])).
% 3.92/0.99  
% 3.92/0.99  fof(f19,plain,(
% 3.92/0.99    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.92/0.99    inference(rectify,[],[f18])).
% 3.92/0.99  
% 3.92/0.99  fof(f21,plain,(
% 3.92/0.99    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f20,plain,(
% 3.92/0.99    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f22,plain,(
% 3.92/0.99    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f21,f20])).
% 3.92/0.99  
% 3.92/0.99  fof(f37,plain,(
% 3.92/0.99    ( ! [X2,X0,X3] : (v1_relat_1(X0) | k4_tarski(X2,X3) != sK1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f22])).
% 3.92/0.99  
% 3.92/0.99  fof(f35,plain,(
% 3.92/0.99    ( ! [X4,X0] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f22])).
% 3.92/0.99  
% 3.92/0.99  fof(f4,axiom,(
% 3.92/0.99    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f9,plain,(
% 3.92/0.99    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f4])).
% 3.92/0.99  
% 3.92/0.99  fof(f10,plain,(
% 3.92/0.99    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(flattening,[],[f9])).
% 3.92/0.99  
% 3.92/0.99  fof(f23,plain,(
% 3.92/0.99    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(nnf_transformation,[],[f10])).
% 3.92/0.99  
% 3.92/0.99  fof(f24,plain,(
% 3.92/0.99    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(rectify,[],[f23])).
% 3.92/0.99  
% 3.92/0.99  fof(f25,plain,(
% 3.92/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f26,plain,(
% 3.92/0.99    ! [X0] : (((v4_relat_2(X0) | (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).
% 3.92/0.99  
% 3.92/0.99  fof(f39,plain,(
% 3.92/0.99    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f26])).
% 3.92/0.99  
% 3.92/0.99  fof(f3,axiom,(
% 3.92/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f8,plain,(
% 3.92/0.99    ! [X0] : (! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 3.92/0.99    inference(ennf_transformation,[],[f3])).
% 3.92/0.99  
% 3.92/0.99  fof(f38,plain,(
% 3.92/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f8])).
% 3.92/0.99  
% 3.92/0.99  fof(f36,plain,(
% 3.92/0.99    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f22])).
% 3.92/0.99  
% 3.92/0.99  fof(f42,plain,(
% 3.92/0.99    ( ! [X0] : (v4_relat_2(X0) | sK4(X0) != sK5(X0) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f26])).
% 3.92/0.99  
% 3.92/0.99  fof(f5,conjecture,(
% 3.92/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 3.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.92/0.99  
% 3.92/0.99  fof(f6,negated_conjecture,(
% 3.92/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 3.92/0.99    inference(negated_conjecture,[],[f5])).
% 3.92/0.99  
% 3.92/0.99  fof(f11,plain,(
% 3.92/0.99    ? [X0,X1] : ((~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1)) & v1_relat_1(X1))),
% 3.92/0.99    inference(ennf_transformation,[],[f6])).
% 3.92/0.99  
% 3.92/0.99  fof(f12,plain,(
% 3.92/0.99    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1))),
% 3.92/0.99    inference(flattening,[],[f11])).
% 3.92/0.99  
% 3.92/0.99  fof(f27,plain,(
% 3.92/0.99    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1)) => (~v4_relat_2(k2_wellord1(sK7,sK6)) & v4_relat_2(sK7) & v1_relat_1(sK7))),
% 3.92/0.99    introduced(choice_axiom,[])).
% 3.92/0.99  
% 3.92/0.99  fof(f28,plain,(
% 3.92/0.99    ~v4_relat_2(k2_wellord1(sK7,sK6)) & v4_relat_2(sK7) & v1_relat_1(sK7)),
% 3.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f12,f27])).
% 3.92/0.99  
% 3.92/0.99  fof(f45,plain,(
% 3.92/0.99    ~v4_relat_2(k2_wellord1(sK7,sK6))),
% 3.92/0.99    inference(cnf_transformation,[],[f28])).
% 3.92/0.99  
% 3.92/0.99  fof(f41,plain,(
% 3.92/0.99    ( ! [X0] : (v4_relat_2(X0) | r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f26])).
% 3.92/0.99  
% 3.92/0.99  fof(f40,plain,(
% 3.92/0.99    ( ! [X0] : (v4_relat_2(X0) | r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) | ~v1_relat_1(X0)) )),
% 3.92/0.99    inference(cnf_transformation,[],[f26])).
% 3.92/0.99  
% 3.92/0.99  fof(f44,plain,(
% 3.92/0.99    v4_relat_2(sK7)),
% 3.92/0.99    inference(cnf_transformation,[],[f28])).
% 3.92/0.99  
% 3.92/0.99  fof(f43,plain,(
% 3.92/0.99    v1_relat_1(sK7)),
% 3.92/0.99    inference(cnf_transformation,[],[f28])).
% 3.92/0.99  
% 3.92/0.99  cnf(c_5,plain,
% 3.92/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.92/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_15543,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_15544,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_15543]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_6,plain,
% 3.92/0.99      ( v1_relat_1(X0) | k4_tarski(X1,X2) != sK1(X0) ),
% 3.92/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_13605,plain,
% 3.92/0.99      ( v1_relat_1(k2_wellord1(sK7,sK6))
% 3.92/0.99      | k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) != sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_13606,plain,
% 3.92/0.99      ( k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) != sK1(k2_wellord1(sK7,sK6))
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_13605]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8,plain,
% 3.92/0.99      ( ~ r2_hidden(X0,X1)
% 3.92/0.99      | ~ v1_relat_1(X1)
% 3.92/0.99      | k4_tarski(sK2(X0),sK3(X0)) = X0 ),
% 3.92/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8098,plain,
% 3.92/0.99      ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7)
% 3.92/0.99      | ~ v1_relat_1(sK7)
% 3.92/0.99      | k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) = sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_8099,plain,
% 3.92/0.99      ( k4_tarski(sK2(sK1(k2_wellord1(sK7,sK6))),sK3(sK1(k2_wellord1(sK7,sK6)))) = sK1(k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) != iProver_top
% 3.92/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_8098]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4037,plain,
% 3.92/0.99      ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_4038,plain,
% 3.92/0.99      ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),sK7) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_4037]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_13,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.92/0.99      | ~ r2_hidden(k4_tarski(X1,X0),X2)
% 3.92/0.99      | ~ v4_relat_2(X2)
% 3.92/0.99      | ~ v1_relat_1(X2)
% 3.92/0.99      | X1 = X0 ),
% 3.92/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3570,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),X0)
% 3.92/0.99      | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),X0)
% 3.92/0.99      | ~ v4_relat_2(X0)
% 3.92/0.99      | ~ v1_relat_1(X0)
% 3.92/0.99      | sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3571,plain,
% 3.92/0.99      ( sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),X0) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),X0) != iProver_top
% 3.92/0.99      | v4_relat_2(X0) != iProver_top
% 3.92/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3570]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3573,plain,
% 3.92/0.99      ( sK5(k2_wellord1(sK7,sK6)) = sK4(k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),sK7) != iProver_top
% 3.92/0.99      | v4_relat_2(sK7) != iProver_top
% 3.92/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_3571]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_572,plain,
% 3.92/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.92/0.99      theory(equality) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1162,plain,
% 3.92/0.99      ( r2_hidden(X0,X1)
% 3.92/0.99      | ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X1 != k2_wellord1(sK7,sK6)
% 3.92/0.99      | X0 != sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_572]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1896,plain,
% 3.92/0.99      ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),X0)
% 3.92/0.99      | ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X0 != k2_wellord1(sK7,sK6)
% 3.92/0.99      | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1162]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3073,plain,
% 3.92/0.99      ( ~ r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
% 3.92/0.99      | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1896]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3074,plain,
% 3.92/0.99      ( k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
% 3.92/0.99      | sK1(k2_wellord1(sK7,sK6)) != sK1(k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6)) != iProver_top
% 3.92/0.99      | r2_hidden(sK1(k2_wellord1(sK7,sK6)),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3073]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3046,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_3047,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),sK7) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3046]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_569,plain,( X0 = X0 ),theory(equality) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2666,plain,
% 3.92/0.99      ( k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) = k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_569]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1281,plain,
% 3.92/0.99      ( r2_hidden(X0,X1)
% 3.92/0.99      | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X1 != k2_wellord1(sK7,sK6)
% 3.92/0.99      | X0 != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_572]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1664,plain,
% 3.92/0.99      ( r2_hidden(X0,k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X0 != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1281]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2665,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1664]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_2667,plain,
% 3.92/0.99      ( k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))) != k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_2665]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1209,plain,
% 3.92/0.99      ( sK1(X0) = sK1(X0) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_569]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1897,plain,
% 3.92/0.99      ( sK1(k2_wellord1(sK7,sK6)) = sK1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1209]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1779,plain,
% 3.92/0.99      ( k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) = k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_569]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1267,plain,
% 3.92/0.99      ( r2_hidden(X0,X1)
% 3.92/0.99      | ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X1 != k2_wellord1(sK7,sK6)
% 3.92/0.99      | X0 != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_572]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1548,plain,
% 3.92/0.99      ( r2_hidden(X0,k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | X0 != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1778,plain,
% 3.92/0.99      ( ~ r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)))
% 3.92/0.99      | k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1780,plain,
% 3.92/0.99      ( k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))) != k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6)))
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) != k2_wellord1(sK7,sK6)
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) != iProver_top
% 3.92/0.99      | r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6))) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_1778]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_9,plain,
% 3.92/0.99      ( ~ v1_relat_1(X0)
% 3.92/0.99      | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
% 3.92/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1549,plain,
% 3.92/0.99      ( ~ v1_relat_1(sK7)
% 3.92/0.99      | k3_xboole_0(sK7,k2_zfmisc_1(sK6,sK6)) = k2_wellord1(sK7,sK6) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_7,plain,
% 3.92/0.99      ( r2_hidden(sK1(X0),X0) | v1_relat_1(X0) ),
% 3.92/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1121,plain,
% 3.92/0.99      ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6))
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_1122,plain,
% 3.92/0.99      ( r2_hidden(sK1(k2_wellord1(sK7,sK6)),k2_wellord1(sK7,sK6)) = iProver_top
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_10,plain,
% 3.92/0.99      ( v4_relat_2(X0) | ~ v1_relat_1(X0) | sK5(X0) != sK4(X0) ),
% 3.92/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_14,negated_conjecture,
% 3.92/0.99      ( ~ v4_relat_2(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_264,plain,
% 3.92/0.99      ( ~ v1_relat_1(X0)
% 3.92/0.99      | k2_wellord1(sK7,sK6) != X0
% 3.92/0.99      | sK5(X0) != sK4(X0) ),
% 3.92/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_265,plain,
% 3.92/0.99      ( ~ v1_relat_1(k2_wellord1(sK7,sK6))
% 3.92/0.99      | sK5(k2_wellord1(sK7,sK6)) != sK4(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(unflattening,[status(thm)],[c_264]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_266,plain,
% 3.92/0.99      ( sK5(k2_wellord1(sK7,sK6)) != sK4(k2_wellord1(sK7,sK6))
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_11,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
% 3.92/0.99      | v4_relat_2(X0)
% 3.92/0.99      | ~ v1_relat_1(X0) ),
% 3.92/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_254,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
% 3.92/0.99      | ~ v1_relat_1(X0)
% 3.92/0.99      | k2_wellord1(sK7,sK6) != X0 ),
% 3.92/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_255,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | ~ v1_relat_1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_256,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK5(k2_wellord1(sK7,sK6)),sK4(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) = iProver_top
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_12,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
% 3.92/0.99      | v4_relat_2(X0)
% 3.92/0.99      | ~ v1_relat_1(X0) ),
% 3.92/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_244,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)
% 3.92/0.99      | ~ v1_relat_1(X0)
% 3.92/0.99      | k2_wellord1(sK7,sK6) != X0 ),
% 3.92/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_245,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6))
% 3.92/0.99      | ~ v1_relat_1(k2_wellord1(sK7,sK6)) ),
% 3.92/0.99      inference(unflattening,[status(thm)],[c_244]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_246,plain,
% 3.92/0.99      ( r2_hidden(k4_tarski(sK4(k2_wellord1(sK7,sK6)),sK5(k2_wellord1(sK7,sK6))),k2_wellord1(sK7,sK6)) = iProver_top
% 3.92/0.99      | v1_relat_1(k2_wellord1(sK7,sK6)) != iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_15,negated_conjecture,
% 3.92/0.99      ( v4_relat_2(sK7) ),
% 3.92/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_18,plain,
% 3.92/0.99      ( v4_relat_2(sK7) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_16,negated_conjecture,
% 3.92/0.99      ( v1_relat_1(sK7) ),
% 3.92/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(c_17,plain,
% 3.92/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.92/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.92/0.99  
% 3.92/0.99  cnf(contradiction,plain,
% 3.92/0.99      ( $false ),
% 3.92/0.99      inference(minisat,
% 3.92/0.99                [status(thm)],
% 3.92/0.99                [c_15544,c_13606,c_8099,c_4038,c_3573,c_3074,c_3047,
% 3.92/0.99                 c_2666,c_2667,c_1897,c_1779,c_1780,c_1549,c_1122,c_266,
% 3.92/0.99                 c_256,c_246,c_18,c_17,c_16]) ).
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  ------                               Statistics
% 3.92/0.99  
% 3.92/0.99  ------ Selected
% 3.92/0.99  
% 3.92/0.99  total_time:                             0.459
% 3.92/0.99  
%------------------------------------------------------------------------------
