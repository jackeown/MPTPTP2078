%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:42 EST 2020

% Result     : Theorem 11.77s
% Output     : CNFRefutation 11.77s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 412 expanded)
%              Number of clauses        :   70 ( 148 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  387 (1519 expanded)
%              Number of equality atoms :  174 ( 715 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK6 != sK8
        | sK5 != sK7 )
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( sK6 != sK8
      | sK5 != sK7 )
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f41])).

fof(f68,plain,(
    k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( sK6 != sK8
    | sK5 != sK7 ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_883,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_260,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_871,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_3779,plain,
    ( k3_tarski(k1_xboole_0) = X0
    | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_883,c_871])).

cnf(c_24,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3782,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3779,c_24])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_878,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_28,negated_conjecture,
    ( k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_876,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2083,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_876])).

cnf(c_4770,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_2083])).

cnf(c_5836,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK2(k1_xboole_0,sK5),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3782,c_4770])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_57,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_61,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_482,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1097,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1098,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_28498,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK2(k1_xboole_0,sK5),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5836,c_27,c_57,c_61,c_1098])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_891,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4766,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_878])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_877,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5592,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4766,c_877])).

cnf(c_6274,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3782,c_5592])).

cnf(c_17211,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK8,X0) = iProver_top
    | r2_hidden(sK0(sK8,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_6274])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_892,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21393,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK8,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_17211,c_892])).

cnf(c_4,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( sK5 != sK7
    | sK6 != sK8 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1478,plain,
    ( r2_xboole_0(sK5,sK7)
    | ~ r1_tarski(sK5,sK7)
    | sK6 != sK8 ),
    inference(resolution,[status(thm)],[c_4,c_25])).

cnf(c_1887,plain,
    ( r2_xboole_0(sK5,sK7)
    | ~ r1_tarski(sK5,sK7)
    | ~ r1_tarski(sK8,sK6)
    | ~ r1_tarski(sK6,sK8) ),
    inference(resolution,[status(thm)],[c_8,c_1478])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1095,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1096,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_873,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1854,plain,
    ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(sK7,X0)) = iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_873])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_874,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1972,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK5,sK7) = iProver_top
    | r1_tarski(sK8,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_874])).

cnf(c_1998,plain,
    ( r1_tarski(sK5,sK7)
    | ~ r1_tarski(sK8,sK6)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1972])).

cnf(c_1855,plain,
    ( r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_873])).

cnf(c_2296,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK7,sK5) = iProver_top
    | r1_tarski(sK6,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_874])).

cnf(c_2312,plain,
    ( r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK6,sK8)
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2296])).

cnf(c_1889,plain,
    ( ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7)
    | sK6 != sK8 ),
    inference(resolution,[status(thm)],[c_8,c_25])).

cnf(c_2425,plain,
    ( ~ r1_tarski(sK7,sK5)
    | ~ r1_tarski(sK5,sK7)
    | ~ r1_tarski(sK8,sK6)
    | ~ r1_tarski(sK6,sK8) ),
    inference(resolution,[status(thm)],[c_1889,c_8])).

cnf(c_2429,plain,
    ( ~ r1_tarski(sK8,sK6)
    | ~ r1_tarski(sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1887,c_26,c_57,c_61,c_1096,c_1998,c_2312,c_2425])).

cnf(c_2431,plain,
    ( r1_tarski(sK8,sK6) != iProver_top
    | r1_tarski(sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_2090,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_877])).

cnf(c_4771,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_2090])).

cnf(c_5904,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3782,c_4771])).

cnf(c_8869,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5904,c_27,c_57,c_61,c_1098])).

cnf(c_8877,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK0(sK6,X0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_8869])).

cnf(c_9288,plain,
    ( r1_tarski(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_8877,c_892])).

cnf(c_23559,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21393,c_2431,c_9288])).

cnf(c_28504,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28498,c_23559])).

cnf(c_28507,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28504,c_871])).

cnf(c_28516,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3782,c_28507])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28516,c_1096,c_61,c_57,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.77/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.77/2.00  
% 11.77/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.77/2.00  
% 11.77/2.00  ------  iProver source info
% 11.77/2.00  
% 11.77/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.77/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.77/2.00  git: non_committed_changes: false
% 11.77/2.00  git: last_make_outside_of_git: false
% 11.77/2.00  
% 11.77/2.00  ------ 
% 11.77/2.00  ------ Parsing...
% 11.77/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.77/2.00  
% 11.77/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.77/2.00  
% 11.77/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.77/2.00  
% 11.77/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.77/2.00  ------ Proving...
% 11.77/2.00  ------ Problem Properties 
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  clauses                                 27
% 11.77/2.00  conjectures                             4
% 11.77/2.00  EPR                                     8
% 11.77/2.00  Horn                                    21
% 11.77/2.00  unary                                   6
% 11.77/2.00  binary                                  11
% 11.77/2.00  lits                                    59
% 11.77/2.00  lits eq                                 13
% 11.77/2.00  fd_pure                                 0
% 11.77/2.00  fd_pseudo                               0
% 11.77/2.00  fd_cond                                 2
% 11.77/2.00  fd_pseudo_cond                          5
% 11.77/2.00  AC symbols                              0
% 11.77/2.00  
% 11.77/2.00  ------ Input Options Time Limit: Unbounded
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  ------ 
% 11.77/2.00  Current options:
% 11.77/2.00  ------ 
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  ------ Proving...
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  % SZS status Theorem for theBenchmark.p
% 11.77/2.00  
% 11.77/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.77/2.00  
% 11.77/2.00  fof(f7,axiom,(
% 11.77/2.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f33,plain,(
% 11.77/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 11.77/2.00    inference(nnf_transformation,[],[f7])).
% 11.77/2.00  
% 11.77/2.00  fof(f34,plain,(
% 11.77/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.77/2.00    inference(rectify,[],[f33])).
% 11.77/2.00  
% 11.77/2.00  fof(f37,plain,(
% 11.77/2.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 11.77/2.00    introduced(choice_axiom,[])).
% 11.77/2.00  
% 11.77/2.00  fof(f36,plain,(
% 11.77/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 11.77/2.00    introduced(choice_axiom,[])).
% 11.77/2.00  
% 11.77/2.00  fof(f35,plain,(
% 11.77/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 11.77/2.00    introduced(choice_axiom,[])).
% 11.77/2.00  
% 11.77/2.00  fof(f38,plain,(
% 11.77/2.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 11.77/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 11.77/2.00  
% 11.77/2.00  fof(f58,plain,(
% 11.77/2.00    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f38])).
% 11.77/2.00  
% 11.77/2.00  fof(f1,axiom,(
% 11.77/2.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f15,plain,(
% 11.77/2.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 11.77/2.00    inference(unused_predicate_definition_removal,[],[f1])).
% 11.77/2.00  
% 11.77/2.00  fof(f16,plain,(
% 11.77/2.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 11.77/2.00    inference(ennf_transformation,[],[f15])).
% 11.77/2.00  
% 11.77/2.00  fof(f43,plain,(
% 11.77/2.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f16])).
% 11.77/2.00  
% 11.77/2.00  fof(f4,axiom,(
% 11.77/2.00    v1_xboole_0(k1_xboole_0)),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f48,plain,(
% 11.77/2.00    v1_xboole_0(k1_xboole_0)),
% 11.77/2.00    inference(cnf_transformation,[],[f4])).
% 11.77/2.00  
% 11.77/2.00  fof(f11,axiom,(
% 11.77/2.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f67,plain,(
% 11.77/2.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 11.77/2.00    inference(cnf_transformation,[],[f11])).
% 11.77/2.00  
% 11.77/2.00  fof(f8,axiom,(
% 11.77/2.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f39,plain,(
% 11.77/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.77/2.00    inference(nnf_transformation,[],[f8])).
% 11.77/2.00  
% 11.77/2.00  fof(f40,plain,(
% 11.77/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.77/2.00    inference(flattening,[],[f39])).
% 11.77/2.00  
% 11.77/2.00  fof(f62,plain,(
% 11.77/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f40])).
% 11.77/2.00  
% 11.77/2.00  fof(f12,conjecture,(
% 11.77/2.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f13,negated_conjecture,(
% 11.77/2.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.77/2.00    inference(negated_conjecture,[],[f12])).
% 11.77/2.00  
% 11.77/2.00  fof(f23,plain,(
% 11.77/2.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 11.77/2.00    inference(ennf_transformation,[],[f13])).
% 11.77/2.00  
% 11.77/2.00  fof(f24,plain,(
% 11.77/2.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 11.77/2.00    inference(flattening,[],[f23])).
% 11.77/2.00  
% 11.77/2.00  fof(f41,plain,(
% 11.77/2.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK6 != sK8 | sK5 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8))),
% 11.77/2.00    introduced(choice_axiom,[])).
% 11.77/2.00  
% 11.77/2.00  fof(f42,plain,(
% 11.77/2.00    (sK6 != sK8 | sK5 != sK7) & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8)),
% 11.77/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f41])).
% 11.77/2.00  
% 11.77/2.00  fof(f68,plain,(
% 11.77/2.00    k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8)),
% 11.77/2.00    inference(cnf_transformation,[],[f42])).
% 11.77/2.00  
% 11.77/2.00  fof(f60,plain,(
% 11.77/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 11.77/2.00    inference(cnf_transformation,[],[f40])).
% 11.77/2.00  
% 11.77/2.00  fof(f69,plain,(
% 11.77/2.00    k1_xboole_0 != sK5),
% 11.77/2.00    inference(cnf_transformation,[],[f42])).
% 11.77/2.00  
% 11.77/2.00  fof(f6,axiom,(
% 11.77/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f31,plain,(
% 11.77/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.77/2.00    inference(nnf_transformation,[],[f6])).
% 11.77/2.00  
% 11.77/2.00  fof(f32,plain,(
% 11.77/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.77/2.00    inference(flattening,[],[f31])).
% 11.77/2.00  
% 11.77/2.00  fof(f51,plain,(
% 11.77/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.77/2.00    inference(cnf_transformation,[],[f32])).
% 11.77/2.00  
% 11.77/2.00  fof(f73,plain,(
% 11.77/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.77/2.00    inference(equality_resolution,[],[f51])).
% 11.77/2.00  
% 11.77/2.00  fof(f53,plain,(
% 11.77/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f32])).
% 11.77/2.00  
% 11.77/2.00  fof(f2,axiom,(
% 11.77/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f17,plain,(
% 11.77/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.77/2.00    inference(ennf_transformation,[],[f2])).
% 11.77/2.00  
% 11.77/2.00  fof(f25,plain,(
% 11.77/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.00    inference(nnf_transformation,[],[f17])).
% 11.77/2.00  
% 11.77/2.00  fof(f26,plain,(
% 11.77/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.00    inference(rectify,[],[f25])).
% 11.77/2.00  
% 11.77/2.00  fof(f27,plain,(
% 11.77/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.77/2.00    introduced(choice_axiom,[])).
% 11.77/2.00  
% 11.77/2.00  fof(f28,plain,(
% 11.77/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.77/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 11.77/2.00  
% 11.77/2.00  fof(f45,plain,(
% 11.77/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f28])).
% 11.77/2.00  
% 11.77/2.00  fof(f61,plain,(
% 11.77/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 11.77/2.00    inference(cnf_transformation,[],[f40])).
% 11.77/2.00  
% 11.77/2.00  fof(f46,plain,(
% 11.77/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f28])).
% 11.77/2.00  
% 11.77/2.00  fof(f3,axiom,(
% 11.77/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f14,plain,(
% 11.77/2.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 11.77/2.00    inference(unused_predicate_definition_removal,[],[f3])).
% 11.77/2.00  
% 11.77/2.00  fof(f18,plain,(
% 11.77/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 11.77/2.00    inference(ennf_transformation,[],[f14])).
% 11.77/2.00  
% 11.77/2.00  fof(f19,plain,(
% 11.77/2.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 11.77/2.00    inference(flattening,[],[f18])).
% 11.77/2.00  
% 11.77/2.00  fof(f47,plain,(
% 11.77/2.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f19])).
% 11.77/2.00  
% 11.77/2.00  fof(f71,plain,(
% 11.77/2.00    sK6 != sK8 | sK5 != sK7),
% 11.77/2.00    inference(cnf_transformation,[],[f42])).
% 11.77/2.00  
% 11.77/2.00  fof(f70,plain,(
% 11.77/2.00    k1_xboole_0 != sK6),
% 11.77/2.00    inference(cnf_transformation,[],[f42])).
% 11.77/2.00  
% 11.77/2.00  fof(f10,axiom,(
% 11.77/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f22,plain,(
% 11.77/2.00    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 11.77/2.00    inference(ennf_transformation,[],[f10])).
% 11.77/2.00  
% 11.77/2.00  fof(f66,plain,(
% 11.77/2.00    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.77/2.00    inference(cnf_transformation,[],[f22])).
% 11.77/2.00  
% 11.77/2.00  fof(f9,axiom,(
% 11.77/2.00    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 11.77/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.77/2.00  
% 11.77/2.00  fof(f21,plain,(
% 11.77/2.00    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 11.77/2.00    inference(ennf_transformation,[],[f9])).
% 11.77/2.00  
% 11.77/2.00  fof(f63,plain,(
% 11.77/2.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 11.77/2.00    inference(cnf_transformation,[],[f21])).
% 11.77/2.00  
% 11.77/2.00  cnf(c_12,plain,
% 11.77/2.00      ( r2_hidden(sK3(X0,X1),X0)
% 11.77/2.00      | r2_hidden(sK2(X0,X1),X1)
% 11.77/2.00      | k3_tarski(X0) = X1 ),
% 11.77/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_883,plain,
% 11.77/2.00      ( k3_tarski(X0) = X1
% 11.77/2.00      | r2_hidden(sK3(X0,X1),X0) = iProver_top
% 11.77/2.00      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_0,plain,
% 11.77/2.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.77/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_5,plain,
% 11.77/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.77/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_260,plain,
% 11.77/2.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 11.77/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_261,plain,
% 11.77/2.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.77/2.00      inference(unflattening,[status(thm)],[c_260]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_871,plain,
% 11.77/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_3779,plain,
% 11.77/2.00      ( k3_tarski(k1_xboole_0) = X0
% 11.77/2.00      | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_883,c_871]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_24,plain,
% 11.77/2.00      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 11.77/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_3782,plain,
% 11.77/2.00      ( k1_xboole_0 = X0
% 11.77/2.00      | r2_hidden(sK2(k1_xboole_0,X0),X0) = iProver_top ),
% 11.77/2.00      inference(demodulation,[status(thm)],[c_3779,c_24]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_17,plain,
% 11.77/2.00      ( ~ r2_hidden(X0,X1)
% 11.77/2.00      | ~ r2_hidden(X2,X3)
% 11.77/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.77/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_878,plain,
% 11.77/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.77/2.00      | r2_hidden(X2,X3) != iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_28,negated_conjecture,
% 11.77/2.00      ( k2_zfmisc_1(sK5,sK6) = k2_zfmisc_1(sK7,sK8) ),
% 11.77/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_19,plain,
% 11.77/2.00      ( r2_hidden(X0,X1)
% 11.77/2.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 11.77/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_876,plain,
% 11.77/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2083,plain,
% 11.77/2.00      ( r2_hidden(X0,sK7) = iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_28,c_876]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_4770,plain,
% 11.77/2.00      ( r2_hidden(X0,sK7) = iProver_top
% 11.77/2.00      | r2_hidden(X0,sK5) != iProver_top
% 11.77/2.00      | r2_hidden(X1,sK6) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_878,c_2083]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_5836,plain,
% 11.77/2.00      ( sK5 = k1_xboole_0
% 11.77/2.00      | r2_hidden(X0,sK6) != iProver_top
% 11.77/2.00      | r2_hidden(sK2(k1_xboole_0,sK5),sK7) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_3782,c_4770]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_27,negated_conjecture,
% 11.77/2.00      ( k1_xboole_0 != sK5 ),
% 11.77/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_10,plain,
% 11.77/2.00      ( r1_tarski(X0,X0) ),
% 11.77/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_57,plain,
% 11.77/2.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_8,plain,
% 11.77/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.77/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_61,plain,
% 11.77/2.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.77/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_482,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1097,plain,
% 11.77/2.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_482]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1098,plain,
% 11.77/2.00      ( sK5 != k1_xboole_0
% 11.77/2.00      | k1_xboole_0 = sK5
% 11.77/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_1097]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_28498,plain,
% 11.77/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 11.77/2.00      | r2_hidden(sK2(k1_xboole_0,sK5),sK7) = iProver_top ),
% 11.77/2.00      inference(global_propositional_subsumption,
% 11.77/2.00                [status(thm)],
% 11.77/2.00                [c_5836,c_27,c_57,c_61,c_1098]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2,plain,
% 11.77/2.00      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 11.77/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_891,plain,
% 11.77/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.77/2.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_4766,plain,
% 11.77/2.00      ( r2_hidden(X0,sK7) != iProver_top
% 11.77/2.00      | r2_hidden(X1,sK8) != iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_28,c_878]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_18,plain,
% 11.77/2.00      ( r2_hidden(X0,X1)
% 11.77/2.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.77/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_877,plain,
% 11.77/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_5592,plain,
% 11.77/2.00      ( r2_hidden(X0,sK7) != iProver_top
% 11.77/2.00      | r2_hidden(X1,sK8) != iProver_top
% 11.77/2.00      | r2_hidden(X1,sK6) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_4766,c_877]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_6274,plain,
% 11.77/2.00      ( sK7 = k1_xboole_0
% 11.77/2.00      | r2_hidden(X0,sK8) != iProver_top
% 11.77/2.00      | r2_hidden(X0,sK6) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_3782,c_5592]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_17211,plain,
% 11.77/2.00      ( sK7 = k1_xboole_0
% 11.77/2.00      | r1_tarski(sK8,X0) = iProver_top
% 11.77/2.00      | r2_hidden(sK0(sK8,X0),sK6) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_891,c_6274]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1,plain,
% 11.77/2.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 11.77/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_892,plain,
% 11.77/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.77/2.00      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_21393,plain,
% 11.77/2.00      ( sK7 = k1_xboole_0 | r1_tarski(sK8,sK6) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_17211,c_892]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_4,plain,
% 11.77/2.00      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 11.77/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_25,negated_conjecture,
% 11.77/2.00      ( sK5 != sK7 | sK6 != sK8 ),
% 11.77/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1478,plain,
% 11.77/2.00      ( r2_xboole_0(sK5,sK7) | ~ r1_tarski(sK5,sK7) | sK6 != sK8 ),
% 11.77/2.00      inference(resolution,[status(thm)],[c_4,c_25]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1887,plain,
% 11.77/2.00      ( r2_xboole_0(sK5,sK7)
% 11.77/2.00      | ~ r1_tarski(sK5,sK7)
% 11.77/2.00      | ~ r1_tarski(sK8,sK6)
% 11.77/2.00      | ~ r1_tarski(sK6,sK8) ),
% 11.77/2.00      inference(resolution,[status(thm)],[c_8,c_1478]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_26,negated_conjecture,
% 11.77/2.00      ( k1_xboole_0 != sK6 ),
% 11.77/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1095,plain,
% 11.77/2.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_482]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1096,plain,
% 11.77/2.00      ( sK6 != k1_xboole_0
% 11.77/2.00      | k1_xboole_0 = sK6
% 11.77/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.77/2.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_22,plain,
% 11.77/2.00      ( ~ r1_tarski(X0,X1)
% 11.77/2.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 11.77/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_873,plain,
% 11.77/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.77/2.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1854,plain,
% 11.77/2.00      ( r1_tarski(k2_zfmisc_1(sK5,sK6),k2_zfmisc_1(sK7,X0)) = iProver_top
% 11.77/2.00      | r1_tarski(sK8,X0) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_28,c_873]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_21,plain,
% 11.77/2.00      ( r1_tarski(X0,X1)
% 11.77/2.00      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
% 11.77/2.00      | k1_xboole_0 = X2 ),
% 11.77/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_874,plain,
% 11.77/2.00      ( k1_xboole_0 = X0
% 11.77/2.00      | r1_tarski(X1,X2) = iProver_top
% 11.77/2.00      | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1972,plain,
% 11.77/2.00      ( sK6 = k1_xboole_0
% 11.77/2.00      | r1_tarski(sK5,sK7) = iProver_top
% 11.77/2.00      | r1_tarski(sK8,sK6) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_1854,c_874]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1998,plain,
% 11.77/2.00      ( r1_tarski(sK5,sK7) | ~ r1_tarski(sK8,sK6) | sK6 = k1_xboole_0 ),
% 11.77/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1972]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1855,plain,
% 11.77/2.00      ( r1_tarski(X0,sK8) != iProver_top
% 11.77/2.00      | r1_tarski(k2_zfmisc_1(sK7,X0),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_28,c_873]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2296,plain,
% 11.77/2.00      ( sK6 = k1_xboole_0
% 11.77/2.00      | r1_tarski(sK7,sK5) = iProver_top
% 11.77/2.00      | r1_tarski(sK6,sK8) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_1855,c_874]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2312,plain,
% 11.77/2.00      ( r1_tarski(sK7,sK5) | ~ r1_tarski(sK6,sK8) | sK6 = k1_xboole_0 ),
% 11.77/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2296]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_1889,plain,
% 11.77/2.00      ( ~ r1_tarski(sK7,sK5) | ~ r1_tarski(sK5,sK7) | sK6 != sK8 ),
% 11.77/2.00      inference(resolution,[status(thm)],[c_8,c_25]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2425,plain,
% 11.77/2.00      ( ~ r1_tarski(sK7,sK5)
% 11.77/2.00      | ~ r1_tarski(sK5,sK7)
% 11.77/2.00      | ~ r1_tarski(sK8,sK6)
% 11.77/2.00      | ~ r1_tarski(sK6,sK8) ),
% 11.77/2.00      inference(resolution,[status(thm)],[c_1889,c_8]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2429,plain,
% 11.77/2.00      ( ~ r1_tarski(sK8,sK6) | ~ r1_tarski(sK6,sK8) ),
% 11.77/2.00      inference(global_propositional_subsumption,
% 11.77/2.00                [status(thm)],
% 11.77/2.00                [c_1887,c_26,c_57,c_61,c_1096,c_1998,c_2312,c_2425]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2431,plain,
% 11.77/2.00      ( r1_tarski(sK8,sK6) != iProver_top
% 11.77/2.00      | r1_tarski(sK6,sK8) != iProver_top ),
% 11.77/2.00      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_2090,plain,
% 11.77/2.00      ( r2_hidden(X0,sK8) = iProver_top
% 11.77/2.00      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_28,c_877]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_4771,plain,
% 11.77/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 11.77/2.00      | r2_hidden(X1,sK8) = iProver_top
% 11.77/2.00      | r2_hidden(X1,sK6) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_878,c_2090]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_5904,plain,
% 11.77/2.00      ( sK5 = k1_xboole_0
% 11.77/2.00      | r2_hidden(X0,sK8) = iProver_top
% 11.77/2.00      | r2_hidden(X0,sK6) != iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_3782,c_4771]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_8869,plain,
% 11.77/2.00      ( r2_hidden(X0,sK8) = iProver_top
% 11.77/2.00      | r2_hidden(X0,sK6) != iProver_top ),
% 11.77/2.00      inference(global_propositional_subsumption,
% 11.77/2.00                [status(thm)],
% 11.77/2.00                [c_5904,c_27,c_57,c_61,c_1098]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_8877,plain,
% 11.77/2.00      ( r1_tarski(sK6,X0) = iProver_top
% 11.77/2.00      | r2_hidden(sK0(sK6,X0),sK8) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_891,c_8869]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_9288,plain,
% 11.77/2.00      ( r1_tarski(sK6,sK8) = iProver_top ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_8877,c_892]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_23559,plain,
% 11.77/2.00      ( sK7 = k1_xboole_0 ),
% 11.77/2.00      inference(global_propositional_subsumption,
% 11.77/2.00                [status(thm)],
% 11.77/2.00                [c_21393,c_2431,c_9288]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_28504,plain,
% 11.77/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 11.77/2.00      | r2_hidden(sK2(k1_xboole_0,sK5),k1_xboole_0) = iProver_top ),
% 11.77/2.00      inference(light_normalisation,[status(thm)],[c_28498,c_23559]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_28507,plain,
% 11.77/2.00      ( r2_hidden(X0,sK6) != iProver_top ),
% 11.77/2.00      inference(forward_subsumption_resolution,
% 11.77/2.00                [status(thm)],
% 11.77/2.00                [c_28504,c_871]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(c_28516,plain,
% 11.77/2.00      ( sK6 = k1_xboole_0 ),
% 11.77/2.00      inference(superposition,[status(thm)],[c_3782,c_28507]) ).
% 11.77/2.00  
% 11.77/2.00  cnf(contradiction,plain,
% 11.77/2.00      ( $false ),
% 11.77/2.00      inference(minisat,[status(thm)],[c_28516,c_1096,c_61,c_57,c_26]) ).
% 11.77/2.00  
% 11.77/2.00  
% 11.77/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.77/2.00  
% 11.77/2.00  ------                               Statistics
% 11.77/2.00  
% 11.77/2.00  ------ Selected
% 11.77/2.00  
% 11.77/2.00  total_time:                             1.181
% 11.77/2.00  
%------------------------------------------------------------------------------
