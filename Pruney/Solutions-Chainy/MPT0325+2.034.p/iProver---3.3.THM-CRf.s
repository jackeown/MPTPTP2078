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
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 327 expanded)
%              Number of clauses        :   60 (  96 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  371 (1227 expanded)
%              Number of equality atoms :   95 ( 230 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK8,sK10)
        | ~ r1_tarski(sK7,sK9) )
      & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
      & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_tarski(sK8,sK10)
      | ~ r1_tarski(sK7,sK9) )
    & k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f15,f32])).

fof(f56,plain,(
    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f26,f25,f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11414,plain,
    ( ~ r2_hidden(sK3(sK7,sK8,X0),X1)
    | r2_hidden(sK3(sK7,sK8,X0),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_29526,plain,
    ( ~ r2_hidden(sK3(sK7,sK8,X0),X1)
    | r2_hidden(sK3(sK7,sK8,X0),k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(instantiation,[status(thm)],[c_11414])).

cnf(c_29528,plain,
    ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_29526])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11442,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK3(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11448,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_11442])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1049,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

cnf(c_1204,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_1049])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2526,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1204,c_15])).

cnf(c_9,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2880,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | k2_zfmisc_1(X1,sK8) = X2 ),
    inference(resolution,[status(thm)],[c_2526,c_9])).

cnf(c_383,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_382,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1873,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_383,c_382])).

cnf(c_3774,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | X2 = k2_zfmisc_1(X1,sK8) ),
    inference(resolution,[status(thm)],[c_2880,c_1873])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8268,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3774,c_22])).

cnf(c_20,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_50,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_944,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_946,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_384,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2302,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r1_tarski(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_384,c_5])).

cnf(c_2304,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_1242,plain,
    ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
    | r2_hidden(sK2(sK7,sK8,X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2425,plain,
    ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
    | r2_hidden(sK2(sK7,sK8,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_2428,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_2426,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2432,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_8340,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X0,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8268,c_26,c_27,c_50,c_946,c_2304,c_2428,c_2432])).

cnf(c_8341,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7) ),
    inference(renaming,[status(thm)],[c_8340])).

cnf(c_8469,plain,
    ( ~ r2_hidden(sK0(X0,sK9),sK7)
    | r1_tarski(X0,sK9) ),
    inference(resolution,[status(thm)],[c_8341,c_0])).

cnf(c_8479,plain,
    ( r1_tarski(sK7,sK9) ),
    inference(resolution,[status(thm)],[c_8469,c_1])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1194,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_16,c_1049])).

cnf(c_2517,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1194,c_15])).

cnf(c_2844,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r1_tarski(sK7,X1) ),
    inference(resolution,[status(thm)],[c_2517,c_1])).

cnf(c_2906,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10)
    | r1_tarski(sK7,X1) ),
    inference(resolution,[status(thm)],[c_2844,c_0])).

cnf(c_4923,plain,
    ( r1_tarski(sK7,X0)
    | r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_2906,c_1])).

cnf(c_4925,plain,
    ( r1_tarski(sK7,k1_xboole_0)
    | r1_tarski(sK8,sK10) ),
    inference(instantiation,[status(thm)],[c_4923])).

cnf(c_3161,plain,
    ( r2_hidden(sK3(sK7,sK8,X0),X1)
    | ~ r2_hidden(sK3(sK7,sK8,X0),sK7)
    | ~ r1_tarski(sK7,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3163,plain,
    ( ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
    | r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_974,plain,
    ( r2_hidden(sK3(sK7,sK8,X0),sK7)
    | r2_hidden(sK2(sK7,sK8,X0),X0)
    | k2_zfmisc_1(sK7,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_981,plain,
    ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_912,plain,
    ( k2_zfmisc_1(sK7,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_913,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29528,c_11448,c_8479,c_4925,c_3163,c_2432,c_2428,c_2304,c_981,c_946,c_913,c_50,c_27,c_26,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:46:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.84/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.52  
% 7.84/1.52  ------  iProver source info
% 7.84/1.52  
% 7.84/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.52  git: non_committed_changes: false
% 7.84/1.52  git: last_make_outside_of_git: false
% 7.84/1.52  
% 7.84/1.52  ------ 
% 7.84/1.52  ------ Parsing...
% 7.84/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.52  
% 7.84/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.52  ------ Proving...
% 7.84/1.52  ------ Problem Properties 
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  clauses                                 23
% 7.84/1.52  conjectures                             3
% 7.84/1.52  EPR                                     3
% 7.84/1.52  Horn                                    17
% 7.84/1.52  unary                                   6
% 7.84/1.52  binary                                  10
% 7.84/1.52  lits                                    49
% 7.84/1.52  lits eq                                 14
% 7.84/1.52  fd_pure                                 0
% 7.84/1.52  fd_pseudo                               0
% 7.84/1.52  fd_cond                                 1
% 7.84/1.52  fd_pseudo_cond                          4
% 7.84/1.52  AC symbols                              0
% 7.84/1.52  
% 7.84/1.52  ------ Input Options Time Limit: Unbounded
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  ------ 
% 7.84/1.52  Current options:
% 7.84/1.52  ------ 
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  ------ Proving...
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  % SZS status Theorem for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  fof(f1,axiom,(
% 7.84/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f12,plain,(
% 7.84/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.84/1.52    inference(ennf_transformation,[],[f1])).
% 7.84/1.52  
% 7.84/1.52  fof(f16,plain,(
% 7.84/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.52    inference(nnf_transformation,[],[f12])).
% 7.84/1.52  
% 7.84/1.52  fof(f17,plain,(
% 7.84/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.52    inference(rectify,[],[f16])).
% 7.84/1.52  
% 7.84/1.52  fof(f18,plain,(
% 7.84/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f19,plain,(
% 7.84/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 7.84/1.52  
% 7.84/1.52  fof(f34,plain,(
% 7.84/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f19])).
% 7.84/1.52  
% 7.84/1.52  fof(f2,axiom,(
% 7.84/1.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f11,plain,(
% 7.84/1.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.84/1.52    inference(rectify,[],[f2])).
% 7.84/1.52  
% 7.84/1.52  fof(f13,plain,(
% 7.84/1.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.84/1.52    inference(ennf_transformation,[],[f11])).
% 7.84/1.52  
% 7.84/1.52  fof(f20,plain,(
% 7.84/1.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f21,plain,(
% 7.84/1.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.84/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 7.84/1.52  
% 7.84/1.52  fof(f38,plain,(
% 7.84/1.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.84/1.52    inference(cnf_transformation,[],[f21])).
% 7.84/1.52  
% 7.84/1.52  fof(f4,axiom,(
% 7.84/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f40,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.84/1.52    inference(cnf_transformation,[],[f4])).
% 7.84/1.52  
% 7.84/1.52  fof(f59,plain,(
% 7.84/1.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.84/1.52    inference(definition_unfolding,[],[f38,f40])).
% 7.84/1.52  
% 7.84/1.52  fof(f7,axiom,(
% 7.84/1.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f28,plain,(
% 7.84/1.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.84/1.52    inference(nnf_transformation,[],[f7])).
% 7.84/1.52  
% 7.84/1.52  fof(f29,plain,(
% 7.84/1.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.84/1.52    inference(flattening,[],[f28])).
% 7.84/1.52  
% 7.84/1.52  fof(f50,plain,(
% 7.84/1.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.84/1.52    inference(cnf_transformation,[],[f29])).
% 7.84/1.52  
% 7.84/1.52  fof(f9,conjecture,(
% 7.84/1.52    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f10,negated_conjecture,(
% 7.84/1.52    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 7.84/1.52    inference(negated_conjecture,[],[f9])).
% 7.84/1.52  
% 7.84/1.52  fof(f14,plain,(
% 7.84/1.52    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 7.84/1.52    inference(ennf_transformation,[],[f10])).
% 7.84/1.52  
% 7.84/1.52  fof(f15,plain,(
% 7.84/1.52    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 7.84/1.52    inference(flattening,[],[f14])).
% 7.84/1.52  
% 7.84/1.52  fof(f32,plain,(
% 7.84/1.52    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f33,plain,(
% 7.84/1.52    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 7.84/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f15,f32])).
% 7.84/1.52  
% 7.84/1.52  fof(f56,plain,(
% 7.84/1.52    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 7.84/1.52    inference(cnf_transformation,[],[f33])).
% 7.84/1.52  
% 7.84/1.52  fof(f52,plain,(
% 7.84/1.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f29])).
% 7.84/1.52  
% 7.84/1.52  fof(f6,axiom,(
% 7.84/1.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f22,plain,(
% 7.84/1.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.84/1.52    inference(nnf_transformation,[],[f6])).
% 7.84/1.52  
% 7.84/1.52  fof(f23,plain,(
% 7.84/1.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.84/1.52    inference(rectify,[],[f22])).
% 7.84/1.52  
% 7.84/1.52  fof(f26,plain,(
% 7.84/1.52    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f25,plain,(
% 7.84/1.52    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f24,plain,(
% 7.84/1.52    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.84/1.52    introduced(choice_axiom,[])).
% 7.84/1.52  
% 7.84/1.52  fof(f27,plain,(
% 7.84/1.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 7.84/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f26,f25,f24])).
% 7.84/1.52  
% 7.84/1.52  fof(f47,plain,(
% 7.84/1.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f27])).
% 7.84/1.52  
% 7.84/1.52  fof(f57,plain,(
% 7.84/1.52    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 7.84/1.52    inference(cnf_transformation,[],[f33])).
% 7.84/1.52  
% 7.84/1.52  fof(f8,axiom,(
% 7.84/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f30,plain,(
% 7.84/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.84/1.52    inference(nnf_transformation,[],[f8])).
% 7.84/1.52  
% 7.84/1.52  fof(f31,plain,(
% 7.84/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.84/1.52    inference(flattening,[],[f30])).
% 7.84/1.52  
% 7.84/1.52  fof(f53,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f31])).
% 7.84/1.52  
% 7.84/1.52  fof(f54,plain,(
% 7.84/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.84/1.52    inference(cnf_transformation,[],[f31])).
% 7.84/1.52  
% 7.84/1.52  fof(f68,plain,(
% 7.84/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.84/1.52    inference(equality_resolution,[],[f54])).
% 7.84/1.52  
% 7.84/1.52  fof(f5,axiom,(
% 7.84/1.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f41,plain,(
% 7.84/1.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f5])).
% 7.84/1.52  
% 7.84/1.52  fof(f36,plain,(
% 7.84/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f19])).
% 7.84/1.52  
% 7.84/1.52  fof(f35,plain,(
% 7.84/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f19])).
% 7.84/1.52  
% 7.84/1.52  fof(f3,axiom,(
% 7.84/1.52    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.84/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.52  
% 7.84/1.52  fof(f39,plain,(
% 7.84/1.52    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.84/1.52    inference(cnf_transformation,[],[f3])).
% 7.84/1.52  
% 7.84/1.52  fof(f61,plain,(
% 7.84/1.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.84/1.52    inference(definition_unfolding,[],[f39,f40])).
% 7.84/1.52  
% 7.84/1.52  fof(f51,plain,(
% 7.84/1.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.84/1.52    inference(cnf_transformation,[],[f29])).
% 7.84/1.52  
% 7.84/1.52  fof(f46,plain,(
% 7.84/1.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.84/1.52    inference(cnf_transformation,[],[f27])).
% 7.84/1.52  
% 7.84/1.52  fof(f58,plain,(
% 7.84/1.52    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 7.84/1.52    inference(cnf_transformation,[],[f33])).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2,plain,
% 7.84/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.84/1.52      inference(cnf_transformation,[],[f34]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_11414,plain,
% 7.84/1.52      ( ~ r2_hidden(sK3(sK7,sK8,X0),X1)
% 7.84/1.52      | r2_hidden(sK3(sK7,sK8,X0),X2)
% 7.84/1.52      | ~ r1_tarski(X1,X2) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_29526,plain,
% 7.84/1.52      ( ~ r2_hidden(sK3(sK7,sK8,X0),X1)
% 7.84/1.52      | r2_hidden(sK3(sK7,sK8,X0),k4_xboole_0(X2,k4_xboole_0(X2,X3)))
% 7.84/1.52      | ~ r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_11414]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_29528,plain,
% 7.84/1.52      ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.84/1.52      | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.84/1.52      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_29526]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3,plain,
% 7.84/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.84/1.52      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.84/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_11442,plain,
% 7.84/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.84/1.52      | ~ r2_hidden(sK3(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_11448,plain,
% 7.84/1.52      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.84/1.52      | ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_11442]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_17,plain,
% 7.84/1.52      ( r2_hidden(X0,X1)
% 7.84/1.52      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_23,negated_conjecture,
% 7.84/1.52      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1049,plain,
% 7.84/1.52      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 7.84/1.52      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2,c_23]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1204,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9)
% 7.84/1.52      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_17,c_1049]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_15,plain,
% 7.84/1.52      ( ~ r2_hidden(X0,X1)
% 7.84/1.52      | ~ r2_hidden(X2,X3)
% 7.84/1.52      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2526,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_1204,c_15]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_9,plain,
% 7.84/1.52      ( r2_hidden(sK4(X0,X1,X2),X1)
% 7.84/1.52      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.84/1.52      | k2_zfmisc_1(X0,X1) = X2 ),
% 7.84/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2880,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9)
% 7.84/1.52      | ~ r2_hidden(X0,sK7)
% 7.84/1.52      | r2_hidden(sK2(X1,sK8,X2),X2)
% 7.84/1.52      | k2_zfmisc_1(X1,sK8) = X2 ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2526,c_9]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_383,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_382,plain,( X0 = X0 ),theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1873,plain,
% 7.84/1.52      ( X0 != X1 | X1 = X0 ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_383,c_382]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3774,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9)
% 7.84/1.52      | ~ r2_hidden(X0,sK7)
% 7.84/1.52      | r2_hidden(sK2(X1,sK8,X2),X2)
% 7.84/1.52      | X2 = k2_zfmisc_1(X1,sK8) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2880,c_1873]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_22,negated_conjecture,
% 7.84/1.52      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 7.84/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8268,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9)
% 7.84/1.52      | ~ r2_hidden(X0,sK7)
% 7.84/1.52      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_3774,c_22]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_20,plain,
% 7.84/1.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.84/1.52      | k1_xboole_0 = X1
% 7.84/1.52      | k1_xboole_0 = X0 ),
% 7.84/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_26,plain,
% 7.84/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.84/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_20]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_19,plain,
% 7.84/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.84/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_27,plain,
% 7.84/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_19]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_6,plain,
% 7.84/1.52      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.84/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_50,plain,
% 7.84/1.52      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_0,plain,
% 7.84/1.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.84/1.52      inference(cnf_transformation,[],[f36]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1,plain,
% 7.84/1.52      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.84/1.52      inference(cnf_transformation,[],[f35]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_944,plain,
% 7.84/1.52      ( r1_tarski(X0,X0) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_946,plain,
% 7.84/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_944]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_384,plain,
% 7.84/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.52      theory(equality) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_5,plain,
% 7.84/1.52      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.84/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2302,plain,
% 7.84/1.52      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
% 7.84/1.52      | ~ r1_tarski(X2,k1_xboole_0)
% 7.84/1.52      | X0 != X2 ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_384,c_5]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2304,plain,
% 7.84/1.52      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.84/1.52      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.84/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2302]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1242,plain,
% 7.84/1.52      ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
% 7.84/1.52      | r2_hidden(sK2(sK7,sK8,X0),X1)
% 7.84/1.52      | ~ r1_tarski(X0,X1) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2425,plain,
% 7.84/1.52      ( ~ r2_hidden(sK2(sK7,sK8,X0),X0)
% 7.84/1.52      | r2_hidden(sK2(sK7,sK8,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.84/1.52      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_1242]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2428,plain,
% 7.84/1.52      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 7.84/1.52      | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.84/1.52      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2425]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2426,plain,
% 7.84/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.84/1.52      | ~ r2_hidden(sK2(sK7,sK8,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2432,plain,
% 7.84/1.52      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 7.84/1.52      | ~ r2_hidden(sK2(sK7,sK8,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2426]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8340,plain,
% 7.84/1.52      ( ~ r2_hidden(X0,sK7) | r2_hidden(X0,sK9) ),
% 7.84/1.52      inference(global_propositional_subsumption,
% 7.84/1.52                [status(thm)],
% 7.84/1.52                [c_8268,c_26,c_27,c_50,c_946,c_2304,c_2428,c_2432]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8341,plain,
% 7.84/1.52      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) ),
% 7.84/1.52      inference(renaming,[status(thm)],[c_8340]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8469,plain,
% 7.84/1.52      ( ~ r2_hidden(sK0(X0,sK9),sK7) | r1_tarski(X0,sK9) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_8341,c_0]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_8479,plain,
% 7.84/1.52      ( r1_tarski(sK7,sK9) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_8469,c_1]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_16,plain,
% 7.84/1.52      ( r2_hidden(X0,X1)
% 7.84/1.52      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.84/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_1194,plain,
% 7.84/1.52      ( r2_hidden(X0,sK10)
% 7.84/1.52      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_16,c_1049]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2517,plain,
% 7.84/1.52      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_1194,c_15]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2844,plain,
% 7.84/1.52      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) | r1_tarski(sK7,X1) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2517,c_1]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_2906,plain,
% 7.84/1.52      ( ~ r2_hidden(sK0(X0,sK10),sK8)
% 7.84/1.52      | r1_tarski(X0,sK10)
% 7.84/1.52      | r1_tarski(sK7,X1) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2844,c_0]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_4923,plain,
% 7.84/1.52      ( r1_tarski(sK7,X0) | r1_tarski(sK8,sK10) ),
% 7.84/1.52      inference(resolution,[status(thm)],[c_2906,c_1]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_4925,plain,
% 7.84/1.52      ( r1_tarski(sK7,k1_xboole_0) | r1_tarski(sK8,sK10) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_4923]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3161,plain,
% 7.84/1.52      ( r2_hidden(sK3(sK7,sK8,X0),X1)
% 7.84/1.52      | ~ r2_hidden(sK3(sK7,sK8,X0),sK7)
% 7.84/1.52      | ~ r1_tarski(sK7,X1) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_3163,plain,
% 7.84/1.52      ( ~ r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
% 7.84/1.52      | r2_hidden(sK3(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.84/1.52      | ~ r1_tarski(sK7,k1_xboole_0) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_3161]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_10,plain,
% 7.84/1.52      ( r2_hidden(sK3(X0,X1,X2),X0)
% 7.84/1.52      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.84/1.52      | k2_zfmisc_1(X0,X1) = X2 ),
% 7.84/1.52      inference(cnf_transformation,[],[f46]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_974,plain,
% 7.84/1.52      ( r2_hidden(sK3(sK7,sK8,X0),sK7)
% 7.84/1.52      | r2_hidden(sK2(sK7,sK8,X0),X0)
% 7.84/1.52      | k2_zfmisc_1(sK7,sK8) = X0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_981,plain,
% 7.84/1.52      ( r2_hidden(sK3(sK7,sK8,k1_xboole_0),sK7)
% 7.84/1.52      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 7.84/1.52      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_974]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_912,plain,
% 7.84/1.52      ( k2_zfmisc_1(sK7,sK8) != X0
% 7.84/1.52      | k1_xboole_0 != X0
% 7.84/1.52      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_383]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_913,plain,
% 7.84/1.52      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 7.84/1.52      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 7.84/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.84/1.52      inference(instantiation,[status(thm)],[c_912]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(c_21,negated_conjecture,
% 7.84/1.52      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 7.84/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.84/1.52  
% 7.84/1.52  cnf(contradiction,plain,
% 7.84/1.52      ( $false ),
% 7.84/1.52      inference(minisat,
% 7.84/1.52                [status(thm)],
% 7.84/1.52                [c_29528,c_11448,c_8479,c_4925,c_3163,c_2432,c_2428,
% 7.84/1.52                 c_2304,c_981,c_946,c_913,c_50,c_27,c_26,c_21,c_22]) ).
% 7.84/1.52  
% 7.84/1.52  
% 7.84/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.52  
% 7.84/1.52  ------                               Statistics
% 7.84/1.52  
% 7.84/1.52  ------ Selected
% 7.84/1.52  
% 7.84/1.52  total_time:                             0.903
% 7.84/1.52  
%------------------------------------------------------------------------------
