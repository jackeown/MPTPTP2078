%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:43 EST 2020

% Result     : Theorem 11.79s
% Output     : CNFRefutation 11.79s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 882 expanded)
%              Number of clauses        :   84 ( 295 expanded)
%              Number of leaves         :   17 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          :  451 (3754 expanded)
%              Number of equality atoms :  261 (1889 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK8 != sK10
        | sK7 != sK9 )
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( sK8 != sK10
      | sK7 != sK9 )
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f15,f34])).

fof(f60,plain,(
    k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,
    ( sK8 != sK10
    | sK7 != sK9 ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f62,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

cnf(c_13,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_566,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_574,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1634,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_574])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_51,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1658,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1634,c_51])).

cnf(c_1659,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1658])).

cnf(c_2412,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK3(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_1659])).

cnf(c_27,negated_conjecture,
    ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_563,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_576,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1872,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_565])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_560,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3036,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X1,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_560])).

cnf(c_8308,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_3036])).

cnf(c_16941,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,sK10)) != iProver_top
    | r2_hidden(sK0(sK9,X2),sK7) = iProver_top
    | r1_tarski(sK9,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_8308])).

cnf(c_39285,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_16941])).

cnf(c_40533,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
    | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
    | r1_tarski(sK9,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_39285])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_577,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_40932,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
    | r1_tarski(sK9,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_40533,c_577])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( sK7 != sK9
    | sK8 != sK10 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1063,plain,
    ( ~ r1_tarski(sK9,sK7)
    | ~ r1_tarski(sK7,sK9)
    | sK8 != sK10 ),
    inference(resolution,[status(thm)],[c_5,c_24])).

cnf(c_1189,plain,
    ( ~ r1_tarski(sK9,sK7)
    | ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK10,sK8)
    | ~ r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_1063,c_5])).

cnf(c_1190,plain,
    ( r1_tarski(sK9,sK7) != iProver_top
    | r1_tarski(sK7,sK9) != iProver_top
    | r1_tarski(sK10,sK8) != iProver_top
    | r1_tarski(sK8,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_12,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_567,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2833,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = X1
    | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_1659])).

cnf(c_21,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2843,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2833,c_21])).

cnf(c_832,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_560])).

cnf(c_2066,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_832])).

cnf(c_5361,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_2066])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_271,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_757,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_758,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_5669,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5361,c_25,c_28,c_29,c_758])).

cnf(c_5677,plain,
    ( r2_hidden(sK0(sK7,X0),sK9) = iProver_top
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_5669])).

cnf(c_6111,plain,
    ( r1_tarski(sK7,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5677,c_577])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_561,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_831,plain,
    ( r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_561])).

cnf(c_1901,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_831])).

cnf(c_5218,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK8,X1),sK10) = iProver_top
    | r1_tarski(sK8,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_1901])).

cnf(c_15543,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK0(sK8,X0),sK10) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_5218])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_759,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_760,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_15991,plain,
    ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
    | r1_tarski(sK8,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15543,c_26,c_28,c_29,c_760])).

cnf(c_15999,plain,
    ( r1_tarski(sK8,sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_15991,c_577])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_562,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3035,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_561])).

cnf(c_8018,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,X1)) != iProver_top
    | r2_hidden(X2,sK10) != iProver_top
    | r2_hidden(X2,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_562,c_3035])).

cnf(c_19881,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_8018])).

cnf(c_20123,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X1,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_19881])).

cnf(c_20768,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
    | r2_hidden(sK0(sK10,X1),sK8) = iProver_top
    | r1_tarski(sK10,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_20123])).

cnf(c_37245,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
    | r1_tarski(sK10,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_20768,c_577])).

cnf(c_42084,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_40932,c_1190,c_6111,c_15999,c_37245])).

cnf(c_42111,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_42084,c_23])).

cnf(c_731,plain,
    ( k2_zfmisc_1(sK7,X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_807,plain,
    ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_940,plain,
    ( k2_zfmisc_1(sK7,sK8) != X0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1421,plain,
    ( k2_zfmisc_1(sK7,sK8) != k2_zfmisc_1(sK7,sK8)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_270,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1422,plain,
    ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_2603,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_42637,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42111,c_26,c_25,c_807,c_1190,c_1421,c_1422,c_2603,c_6111,c_15999,c_37245,c_40932])).

cnf(c_42787,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_42637,c_26])).

cnf(c_42808,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_42787])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:34 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.79/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.79/1.99  
% 11.79/1.99  ------  iProver source info
% 11.79/1.99  
% 11.79/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.79/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.79/1.99  git: non_committed_changes: false
% 11.79/1.99  git: last_make_outside_of_git: false
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  
% 11.79/1.99  ------ Input Options
% 11.79/1.99  
% 11.79/1.99  --out_options                           all
% 11.79/1.99  --tptp_safe_out                         true
% 11.79/1.99  --problem_path                          ""
% 11.79/1.99  --include_path                          ""
% 11.79/1.99  --clausifier                            res/vclausify_rel
% 11.79/1.99  --clausifier_options                    --mode clausify
% 11.79/1.99  --stdin                                 false
% 11.79/1.99  --stats_out                             sel
% 11.79/1.99  
% 11.79/1.99  ------ General Options
% 11.79/1.99  
% 11.79/1.99  --fof                                   false
% 11.79/1.99  --time_out_real                         604.99
% 11.79/1.99  --time_out_virtual                      -1.
% 11.79/1.99  --symbol_type_check                     false
% 11.79/1.99  --clausify_out                          false
% 11.79/1.99  --sig_cnt_out                           false
% 11.79/1.99  --trig_cnt_out                          false
% 11.79/1.99  --trig_cnt_out_tolerance                1.
% 11.79/1.99  --trig_cnt_out_sk_spl                   false
% 11.79/1.99  --abstr_cl_out                          false
% 11.79/1.99  
% 11.79/1.99  ------ Global Options
% 11.79/1.99  
% 11.79/1.99  --schedule                              none
% 11.79/1.99  --add_important_lit                     false
% 11.79/1.99  --prop_solver_per_cl                    1000
% 11.79/1.99  --min_unsat_core                        false
% 11.79/1.99  --soft_assumptions                      false
% 11.79/1.99  --soft_lemma_size                       3
% 11.79/1.99  --prop_impl_unit_size                   0
% 11.79/1.99  --prop_impl_unit                        []
% 11.79/1.99  --share_sel_clauses                     true
% 11.79/1.99  --reset_solvers                         false
% 11.79/1.99  --bc_imp_inh                            [conj_cone]
% 11.79/1.99  --conj_cone_tolerance                   3.
% 11.79/1.99  --extra_neg_conj                        none
% 11.79/1.99  --large_theory_mode                     true
% 11.79/1.99  --prolific_symb_bound                   200
% 11.79/1.99  --lt_threshold                          2000
% 11.79/1.99  --clause_weak_htbl                      true
% 11.79/1.99  --gc_record_bc_elim                     false
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing Options
% 11.79/1.99  
% 11.79/1.99  --preprocessing_flag                    true
% 11.79/1.99  --time_out_prep_mult                    0.1
% 11.79/1.99  --splitting_mode                        input
% 11.79/1.99  --splitting_grd                         true
% 11.79/1.99  --splitting_cvd                         false
% 11.79/1.99  --splitting_cvd_svl                     false
% 11.79/1.99  --splitting_nvd                         32
% 11.79/1.99  --sub_typing                            true
% 11.79/1.99  --prep_gs_sim                           false
% 11.79/1.99  --prep_unflatten                        true
% 11.79/1.99  --prep_res_sim                          true
% 11.79/1.99  --prep_upred                            true
% 11.79/1.99  --prep_sem_filter                       exhaustive
% 11.79/1.99  --prep_sem_filter_out                   false
% 11.79/1.99  --pred_elim                             false
% 11.79/1.99  --res_sim_input                         true
% 11.79/1.99  --eq_ax_congr_red                       true
% 11.79/1.99  --pure_diseq_elim                       true
% 11.79/1.99  --brand_transform                       false
% 11.79/1.99  --non_eq_to_eq                          false
% 11.79/1.99  --prep_def_merge                        true
% 11.79/1.99  --prep_def_merge_prop_impl              false
% 11.79/1.99  --prep_def_merge_mbd                    true
% 11.79/1.99  --prep_def_merge_tr_red                 false
% 11.79/1.99  --prep_def_merge_tr_cl                  false
% 11.79/1.99  --smt_preprocessing                     true
% 11.79/1.99  --smt_ac_axioms                         fast
% 11.79/1.99  --preprocessed_out                      false
% 11.79/1.99  --preprocessed_stats                    false
% 11.79/1.99  
% 11.79/1.99  ------ Abstraction refinement Options
% 11.79/1.99  
% 11.79/1.99  --abstr_ref                             []
% 11.79/1.99  --abstr_ref_prep                        false
% 11.79/1.99  --abstr_ref_until_sat                   false
% 11.79/1.99  --abstr_ref_sig_restrict                funpre
% 11.79/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.79/1.99  --abstr_ref_under                       []
% 11.79/1.99  
% 11.79/1.99  ------ SAT Options
% 11.79/1.99  
% 11.79/1.99  --sat_mode                              false
% 11.79/1.99  --sat_fm_restart_options                ""
% 11.79/1.99  --sat_gr_def                            false
% 11.79/1.99  --sat_epr_types                         true
% 11.79/1.99  --sat_non_cyclic_types                  false
% 11.79/1.99  --sat_finite_models                     false
% 11.79/1.99  --sat_fm_lemmas                         false
% 11.79/1.99  --sat_fm_prep                           false
% 11.79/1.99  --sat_fm_uc_incr                        true
% 11.79/1.99  --sat_out_model                         small
% 11.79/1.99  --sat_out_clauses                       false
% 11.79/1.99  
% 11.79/1.99  ------ QBF Options
% 11.79/1.99  
% 11.79/1.99  --qbf_mode                              false
% 11.79/1.99  --qbf_elim_univ                         false
% 11.79/1.99  --qbf_dom_inst                          none
% 11.79/1.99  --qbf_dom_pre_inst                      false
% 11.79/1.99  --qbf_sk_in                             false
% 11.79/1.99  --qbf_pred_elim                         true
% 11.79/1.99  --qbf_split                             512
% 11.79/1.99  
% 11.79/1.99  ------ BMC1 Options
% 11.79/1.99  
% 11.79/1.99  --bmc1_incremental                      false
% 11.79/1.99  --bmc1_axioms                           reachable_all
% 11.79/1.99  --bmc1_min_bound                        0
% 11.79/1.99  --bmc1_max_bound                        -1
% 11.79/1.99  --bmc1_max_bound_default                -1
% 11.79/1.99  --bmc1_symbol_reachability              true
% 11.79/1.99  --bmc1_property_lemmas                  false
% 11.79/1.99  --bmc1_k_induction                      false
% 11.79/1.99  --bmc1_non_equiv_states                 false
% 11.79/1.99  --bmc1_deadlock                         false
% 11.79/1.99  --bmc1_ucm                              false
% 11.79/1.99  --bmc1_add_unsat_core                   none
% 11.79/1.99  --bmc1_unsat_core_children              false
% 11.79/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.79/1.99  --bmc1_out_stat                         full
% 11.79/1.99  --bmc1_ground_init                      false
% 11.79/1.99  --bmc1_pre_inst_next_state              false
% 11.79/1.99  --bmc1_pre_inst_state                   false
% 11.79/1.99  --bmc1_pre_inst_reach_state             false
% 11.79/1.99  --bmc1_out_unsat_core                   false
% 11.79/1.99  --bmc1_aig_witness_out                  false
% 11.79/1.99  --bmc1_verbose                          false
% 11.79/1.99  --bmc1_dump_clauses_tptp                false
% 11.79/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.79/1.99  --bmc1_dump_file                        -
% 11.79/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.79/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.79/1.99  --bmc1_ucm_extend_mode                  1
% 11.79/1.99  --bmc1_ucm_init_mode                    2
% 11.79/1.99  --bmc1_ucm_cone_mode                    none
% 11.79/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.79/1.99  --bmc1_ucm_relax_model                  4
% 11.79/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.79/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.79/1.99  --bmc1_ucm_layered_model                none
% 11.79/1.99  --bmc1_ucm_max_lemma_size               10
% 11.79/1.99  
% 11.79/1.99  ------ AIG Options
% 11.79/1.99  
% 11.79/1.99  --aig_mode                              false
% 11.79/1.99  
% 11.79/1.99  ------ Instantiation Options
% 11.79/1.99  
% 11.79/1.99  --instantiation_flag                    true
% 11.79/1.99  --inst_sos_flag                         false
% 11.79/1.99  --inst_sos_phase                        true
% 11.79/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel_side                     num_symb
% 11.79/1.99  --inst_solver_per_active                1400
% 11.79/1.99  --inst_solver_calls_frac                1.
% 11.79/1.99  --inst_passive_queue_type               priority_queues
% 11.79/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.79/1.99  --inst_passive_queues_freq              [25;2]
% 11.79/1.99  --inst_dismatching                      true
% 11.79/1.99  --inst_eager_unprocessed_to_passive     true
% 11.79/1.99  --inst_prop_sim_given                   true
% 11.79/1.99  --inst_prop_sim_new                     false
% 11.79/1.99  --inst_subs_new                         false
% 11.79/1.99  --inst_eq_res_simp                      false
% 11.79/1.99  --inst_subs_given                       false
% 11.79/1.99  --inst_orphan_elimination               true
% 11.79/1.99  --inst_learning_loop_flag               true
% 11.79/1.99  --inst_learning_start                   3000
% 11.79/1.99  --inst_learning_factor                  2
% 11.79/1.99  --inst_start_prop_sim_after_learn       3
% 11.79/1.99  --inst_sel_renew                        solver
% 11.79/1.99  --inst_lit_activity_flag                true
% 11.79/1.99  --inst_restr_to_given                   false
% 11.79/1.99  --inst_activity_threshold               500
% 11.79/1.99  --inst_out_proof                        true
% 11.79/1.99  
% 11.79/1.99  ------ Resolution Options
% 11.79/1.99  
% 11.79/1.99  --resolution_flag                       true
% 11.79/1.99  --res_lit_sel                           adaptive
% 11.79/1.99  --res_lit_sel_side                      none
% 11.79/1.99  --res_ordering                          kbo
% 11.79/1.99  --res_to_prop_solver                    active
% 11.79/1.99  --res_prop_simpl_new                    false
% 11.79/1.99  --res_prop_simpl_given                  true
% 11.79/1.99  --res_passive_queue_type                priority_queues
% 11.79/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.79/1.99  --res_passive_queues_freq               [15;5]
% 11.79/1.99  --res_forward_subs                      full
% 11.79/1.99  --res_backward_subs                     full
% 11.79/1.99  --res_forward_subs_resolution           true
% 11.79/1.99  --res_backward_subs_resolution          true
% 11.79/1.99  --res_orphan_elimination                true
% 11.79/1.99  --res_time_limit                        2.
% 11.79/1.99  --res_out_proof                         true
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Options
% 11.79/1.99  
% 11.79/1.99  --superposition_flag                    true
% 11.79/1.99  --sup_passive_queue_type                priority_queues
% 11.79/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.79/1.99  --sup_passive_queues_freq               [1;4]
% 11.79/1.99  --demod_completeness_check              fast
% 11.79/1.99  --demod_use_ground                      true
% 11.79/1.99  --sup_to_prop_solver                    passive
% 11.79/1.99  --sup_prop_simpl_new                    true
% 11.79/1.99  --sup_prop_simpl_given                  true
% 11.79/1.99  --sup_fun_splitting                     false
% 11.79/1.99  --sup_smt_interval                      50000
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Simplification Setup
% 11.79/1.99  
% 11.79/1.99  --sup_indices_passive                   []
% 11.79/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.79/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_full_bw                           [BwDemod]
% 11.79/1.99  --sup_immed_triv                        [TrivRules]
% 11.79/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.79/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_immed_bw_main                     []
% 11.79/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.79/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  
% 11.79/1.99  ------ Combination Options
% 11.79/1.99  
% 11.79/1.99  --comb_res_mult                         3
% 11.79/1.99  --comb_sup_mult                         2
% 11.79/1.99  --comb_inst_mult                        10
% 11.79/1.99  
% 11.79/1.99  ------ Debug Options
% 11.79/1.99  
% 11.79/1.99  --dbg_backtrace                         false
% 11.79/1.99  --dbg_dump_prop_clauses                 false
% 11.79/1.99  --dbg_dump_prop_clauses_file            -
% 11.79/1.99  --dbg_out_stat                          false
% 11.79/1.99  ------ Parsing...
% 11.79/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.79/1.99  ------ Proving...
% 11.79/1.99  ------ Problem Properties 
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  clauses                                 26
% 11.79/1.99  conjectures                             4
% 11.79/1.99  EPR                                     7
% 11.79/1.99  Horn                                    20
% 11.79/1.99  unary                                   8
% 11.79/1.99  binary                                  10
% 11.79/1.99  lits                                    54
% 11.79/1.99  lits eq                                 19
% 11.79/1.99  fd_pure                                 0
% 11.79/1.99  fd_pseudo                               0
% 11.79/1.99  fd_cond                                 1
% 11.79/1.99  fd_pseudo_cond                          5
% 11.79/1.99  AC symbols                              0
% 11.79/1.99  
% 11.79/1.99  ------ Input Options Time Limit: Unbounded
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  ------ 
% 11.79/1.99  Current options:
% 11.79/1.99  ------ 
% 11.79/1.99  
% 11.79/1.99  ------ Input Options
% 11.79/1.99  
% 11.79/1.99  --out_options                           all
% 11.79/1.99  --tptp_safe_out                         true
% 11.79/1.99  --problem_path                          ""
% 11.79/1.99  --include_path                          ""
% 11.79/1.99  --clausifier                            res/vclausify_rel
% 11.79/1.99  --clausifier_options                    --mode clausify
% 11.79/1.99  --stdin                                 false
% 11.79/1.99  --stats_out                             sel
% 11.79/1.99  
% 11.79/1.99  ------ General Options
% 11.79/1.99  
% 11.79/1.99  --fof                                   false
% 11.79/1.99  --time_out_real                         604.99
% 11.79/1.99  --time_out_virtual                      -1.
% 11.79/1.99  --symbol_type_check                     false
% 11.79/1.99  --clausify_out                          false
% 11.79/1.99  --sig_cnt_out                           false
% 11.79/1.99  --trig_cnt_out                          false
% 11.79/1.99  --trig_cnt_out_tolerance                1.
% 11.79/1.99  --trig_cnt_out_sk_spl                   false
% 11.79/1.99  --abstr_cl_out                          false
% 11.79/1.99  
% 11.79/1.99  ------ Global Options
% 11.79/1.99  
% 11.79/1.99  --schedule                              none
% 11.79/1.99  --add_important_lit                     false
% 11.79/1.99  --prop_solver_per_cl                    1000
% 11.79/1.99  --min_unsat_core                        false
% 11.79/1.99  --soft_assumptions                      false
% 11.79/1.99  --soft_lemma_size                       3
% 11.79/1.99  --prop_impl_unit_size                   0
% 11.79/1.99  --prop_impl_unit                        []
% 11.79/1.99  --share_sel_clauses                     true
% 11.79/1.99  --reset_solvers                         false
% 11.79/1.99  --bc_imp_inh                            [conj_cone]
% 11.79/1.99  --conj_cone_tolerance                   3.
% 11.79/1.99  --extra_neg_conj                        none
% 11.79/1.99  --large_theory_mode                     true
% 11.79/1.99  --prolific_symb_bound                   200
% 11.79/1.99  --lt_threshold                          2000
% 11.79/1.99  --clause_weak_htbl                      true
% 11.79/1.99  --gc_record_bc_elim                     false
% 11.79/1.99  
% 11.79/1.99  ------ Preprocessing Options
% 11.79/1.99  
% 11.79/1.99  --preprocessing_flag                    true
% 11.79/1.99  --time_out_prep_mult                    0.1
% 11.79/1.99  --splitting_mode                        input
% 11.79/1.99  --splitting_grd                         true
% 11.79/1.99  --splitting_cvd                         false
% 11.79/1.99  --splitting_cvd_svl                     false
% 11.79/1.99  --splitting_nvd                         32
% 11.79/1.99  --sub_typing                            true
% 11.79/1.99  --prep_gs_sim                           false
% 11.79/1.99  --prep_unflatten                        true
% 11.79/1.99  --prep_res_sim                          true
% 11.79/1.99  --prep_upred                            true
% 11.79/1.99  --prep_sem_filter                       exhaustive
% 11.79/1.99  --prep_sem_filter_out                   false
% 11.79/1.99  --pred_elim                             false
% 11.79/1.99  --res_sim_input                         true
% 11.79/1.99  --eq_ax_congr_red                       true
% 11.79/1.99  --pure_diseq_elim                       true
% 11.79/1.99  --brand_transform                       false
% 11.79/1.99  --non_eq_to_eq                          false
% 11.79/1.99  --prep_def_merge                        true
% 11.79/1.99  --prep_def_merge_prop_impl              false
% 11.79/1.99  --prep_def_merge_mbd                    true
% 11.79/1.99  --prep_def_merge_tr_red                 false
% 11.79/1.99  --prep_def_merge_tr_cl                  false
% 11.79/1.99  --smt_preprocessing                     true
% 11.79/1.99  --smt_ac_axioms                         fast
% 11.79/1.99  --preprocessed_out                      false
% 11.79/1.99  --preprocessed_stats                    false
% 11.79/1.99  
% 11.79/1.99  ------ Abstraction refinement Options
% 11.79/1.99  
% 11.79/1.99  --abstr_ref                             []
% 11.79/1.99  --abstr_ref_prep                        false
% 11.79/1.99  --abstr_ref_until_sat                   false
% 11.79/1.99  --abstr_ref_sig_restrict                funpre
% 11.79/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.79/1.99  --abstr_ref_under                       []
% 11.79/1.99  
% 11.79/1.99  ------ SAT Options
% 11.79/1.99  
% 11.79/1.99  --sat_mode                              false
% 11.79/1.99  --sat_fm_restart_options                ""
% 11.79/1.99  --sat_gr_def                            false
% 11.79/1.99  --sat_epr_types                         true
% 11.79/1.99  --sat_non_cyclic_types                  false
% 11.79/1.99  --sat_finite_models                     false
% 11.79/1.99  --sat_fm_lemmas                         false
% 11.79/1.99  --sat_fm_prep                           false
% 11.79/1.99  --sat_fm_uc_incr                        true
% 11.79/1.99  --sat_out_model                         small
% 11.79/1.99  --sat_out_clauses                       false
% 11.79/1.99  
% 11.79/1.99  ------ QBF Options
% 11.79/1.99  
% 11.79/1.99  --qbf_mode                              false
% 11.79/1.99  --qbf_elim_univ                         false
% 11.79/1.99  --qbf_dom_inst                          none
% 11.79/1.99  --qbf_dom_pre_inst                      false
% 11.79/1.99  --qbf_sk_in                             false
% 11.79/1.99  --qbf_pred_elim                         true
% 11.79/1.99  --qbf_split                             512
% 11.79/1.99  
% 11.79/1.99  ------ BMC1 Options
% 11.79/1.99  
% 11.79/1.99  --bmc1_incremental                      false
% 11.79/1.99  --bmc1_axioms                           reachable_all
% 11.79/1.99  --bmc1_min_bound                        0
% 11.79/1.99  --bmc1_max_bound                        -1
% 11.79/1.99  --bmc1_max_bound_default                -1
% 11.79/1.99  --bmc1_symbol_reachability              true
% 11.79/1.99  --bmc1_property_lemmas                  false
% 11.79/1.99  --bmc1_k_induction                      false
% 11.79/1.99  --bmc1_non_equiv_states                 false
% 11.79/1.99  --bmc1_deadlock                         false
% 11.79/1.99  --bmc1_ucm                              false
% 11.79/1.99  --bmc1_add_unsat_core                   none
% 11.79/1.99  --bmc1_unsat_core_children              false
% 11.79/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.79/1.99  --bmc1_out_stat                         full
% 11.79/1.99  --bmc1_ground_init                      false
% 11.79/1.99  --bmc1_pre_inst_next_state              false
% 11.79/1.99  --bmc1_pre_inst_state                   false
% 11.79/1.99  --bmc1_pre_inst_reach_state             false
% 11.79/1.99  --bmc1_out_unsat_core                   false
% 11.79/1.99  --bmc1_aig_witness_out                  false
% 11.79/1.99  --bmc1_verbose                          false
% 11.79/1.99  --bmc1_dump_clauses_tptp                false
% 11.79/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.79/1.99  --bmc1_dump_file                        -
% 11.79/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.79/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.79/1.99  --bmc1_ucm_extend_mode                  1
% 11.79/1.99  --bmc1_ucm_init_mode                    2
% 11.79/1.99  --bmc1_ucm_cone_mode                    none
% 11.79/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.79/1.99  --bmc1_ucm_relax_model                  4
% 11.79/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.79/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.79/1.99  --bmc1_ucm_layered_model                none
% 11.79/1.99  --bmc1_ucm_max_lemma_size               10
% 11.79/1.99  
% 11.79/1.99  ------ AIG Options
% 11.79/1.99  
% 11.79/1.99  --aig_mode                              false
% 11.79/1.99  
% 11.79/1.99  ------ Instantiation Options
% 11.79/1.99  
% 11.79/1.99  --instantiation_flag                    true
% 11.79/1.99  --inst_sos_flag                         false
% 11.79/1.99  --inst_sos_phase                        true
% 11.79/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.79/1.99  --inst_lit_sel_side                     num_symb
% 11.79/1.99  --inst_solver_per_active                1400
% 11.79/1.99  --inst_solver_calls_frac                1.
% 11.79/1.99  --inst_passive_queue_type               priority_queues
% 11.79/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.79/1.99  --inst_passive_queues_freq              [25;2]
% 11.79/1.99  --inst_dismatching                      true
% 11.79/1.99  --inst_eager_unprocessed_to_passive     true
% 11.79/1.99  --inst_prop_sim_given                   true
% 11.79/1.99  --inst_prop_sim_new                     false
% 11.79/1.99  --inst_subs_new                         false
% 11.79/1.99  --inst_eq_res_simp                      false
% 11.79/1.99  --inst_subs_given                       false
% 11.79/1.99  --inst_orphan_elimination               true
% 11.79/1.99  --inst_learning_loop_flag               true
% 11.79/1.99  --inst_learning_start                   3000
% 11.79/1.99  --inst_learning_factor                  2
% 11.79/1.99  --inst_start_prop_sim_after_learn       3
% 11.79/1.99  --inst_sel_renew                        solver
% 11.79/1.99  --inst_lit_activity_flag                true
% 11.79/1.99  --inst_restr_to_given                   false
% 11.79/1.99  --inst_activity_threshold               500
% 11.79/1.99  --inst_out_proof                        true
% 11.79/1.99  
% 11.79/1.99  ------ Resolution Options
% 11.79/1.99  
% 11.79/1.99  --resolution_flag                       true
% 11.79/1.99  --res_lit_sel                           adaptive
% 11.79/1.99  --res_lit_sel_side                      none
% 11.79/1.99  --res_ordering                          kbo
% 11.79/1.99  --res_to_prop_solver                    active
% 11.79/1.99  --res_prop_simpl_new                    false
% 11.79/1.99  --res_prop_simpl_given                  true
% 11.79/1.99  --res_passive_queue_type                priority_queues
% 11.79/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.79/1.99  --res_passive_queues_freq               [15;5]
% 11.79/1.99  --res_forward_subs                      full
% 11.79/1.99  --res_backward_subs                     full
% 11.79/1.99  --res_forward_subs_resolution           true
% 11.79/1.99  --res_backward_subs_resolution          true
% 11.79/1.99  --res_orphan_elimination                true
% 11.79/1.99  --res_time_limit                        2.
% 11.79/1.99  --res_out_proof                         true
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Options
% 11.79/1.99  
% 11.79/1.99  --superposition_flag                    true
% 11.79/1.99  --sup_passive_queue_type                priority_queues
% 11.79/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.79/1.99  --sup_passive_queues_freq               [1;4]
% 11.79/1.99  --demod_completeness_check              fast
% 11.79/1.99  --demod_use_ground                      true
% 11.79/1.99  --sup_to_prop_solver                    passive
% 11.79/1.99  --sup_prop_simpl_new                    true
% 11.79/1.99  --sup_prop_simpl_given                  true
% 11.79/1.99  --sup_fun_splitting                     false
% 11.79/1.99  --sup_smt_interval                      50000
% 11.79/1.99  
% 11.79/1.99  ------ Superposition Simplification Setup
% 11.79/1.99  
% 11.79/1.99  --sup_indices_passive                   []
% 11.79/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.79/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.79/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_full_bw                           [BwDemod]
% 11.79/1.99  --sup_immed_triv                        [TrivRules]
% 11.79/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.79/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_immed_bw_main                     []
% 11.79/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.79/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.79/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.79/1.99  
% 11.79/1.99  ------ Combination Options
% 11.79/1.99  
% 11.79/1.99  --comb_res_mult                         3
% 11.79/1.99  --comb_sup_mult                         2
% 11.79/1.99  --comb_inst_mult                        10
% 11.79/1.99  
% 11.79/1.99  ------ Debug Options
% 11.79/1.99  
% 11.79/1.99  --dbg_backtrace                         false
% 11.79/1.99  --dbg_dump_prop_clauses                 false
% 11.79/1.99  --dbg_dump_prop_clauses_file            -
% 11.79/1.99  --dbg_out_stat                          false
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  ------ Proving...
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  % SZS status Theorem for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99   Resolution empty clause
% 11.79/1.99  
% 11.79/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  fof(f6,axiom,(
% 11.79/1.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f24,plain,(
% 11.79/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.79/1.99    inference(nnf_transformation,[],[f6])).
% 11.79/1.99  
% 11.79/1.99  fof(f25,plain,(
% 11.79/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.79/1.99    inference(rectify,[],[f24])).
% 11.79/1.99  
% 11.79/1.99  fof(f28,plain,(
% 11.79/1.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f27,plain,(
% 11.79/1.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f26,plain,(
% 11.79/1.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f29,plain,(
% 11.79/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 11.79/1.99  
% 11.79/1.99  fof(f50,plain,(
% 11.79/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f29])).
% 11.79/1.99  
% 11.79/1.99  fof(f4,axiom,(
% 11.79/1.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f44,plain,(
% 11.79/1.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f4])).
% 11.79/1.99  
% 11.79/1.99  fof(f2,axiom,(
% 11.79/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f11,plain,(
% 11.79/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.79/1.99    inference(rectify,[],[f2])).
% 11.79/1.99  
% 11.79/1.99  fof(f13,plain,(
% 11.79/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.79/1.99    inference(ennf_transformation,[],[f11])).
% 11.79/1.99  
% 11.79/1.99  fof(f20,plain,(
% 11.79/1.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f21,plain,(
% 11.79/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 11.79/1.99  
% 11.79/1.99  fof(f40,plain,(
% 11.79/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f21])).
% 11.79/1.99  
% 11.79/1.99  fof(f5,axiom,(
% 11.79/1.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f45,plain,(
% 11.79/1.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f5])).
% 11.79/1.99  
% 11.79/1.99  fof(f9,conjecture,(
% 11.79/1.99    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f10,negated_conjecture,(
% 11.79/1.99    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.79/1.99    inference(negated_conjecture,[],[f9])).
% 11.79/1.99  
% 11.79/1.99  fof(f14,plain,(
% 11.79/1.99    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 11.79/1.99    inference(ennf_transformation,[],[f10])).
% 11.79/1.99  
% 11.79/1.99  fof(f15,plain,(
% 11.79/1.99    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 11.79/1.99    inference(flattening,[],[f14])).
% 11.79/1.99  
% 11.79/1.99  fof(f34,plain,(
% 11.79/1.99    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK8 != sK10 | sK7 != sK9) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f35,plain,(
% 11.79/1.99    (sK8 != sK10 | sK7 != sK9) & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10)),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f15,f34])).
% 11.79/1.99  
% 11.79/1.99  fof(f60,plain,(
% 11.79/1.99    k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10)),
% 11.79/1.99    inference(cnf_transformation,[],[f35])).
% 11.79/1.99  
% 11.79/1.99  fof(f47,plain,(
% 11.79/1.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.79/1.99    inference(cnf_transformation,[],[f29])).
% 11.79/1.99  
% 11.79/1.99  fof(f69,plain,(
% 11.79/1.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.79/1.99    inference(equality_resolution,[],[f47])).
% 11.79/1.99  
% 11.79/1.99  fof(f1,axiom,(
% 11.79/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f12,plain,(
% 11.79/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.79/1.99    inference(ennf_transformation,[],[f1])).
% 11.79/1.99  
% 11.79/1.99  fof(f16,plain,(
% 11.79/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.79/1.99    inference(nnf_transformation,[],[f12])).
% 11.79/1.99  
% 11.79/1.99  fof(f17,plain,(
% 11.79/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.79/1.99    inference(rectify,[],[f16])).
% 11.79/1.99  
% 11.79/1.99  fof(f18,plain,(
% 11.79/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.79/1.99    introduced(choice_axiom,[])).
% 11.79/1.99  
% 11.79/1.99  fof(f19,plain,(
% 11.79/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.79/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 11.79/1.99  
% 11.79/1.99  fof(f37,plain,(
% 11.79/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f19])).
% 11.79/1.99  
% 11.79/1.99  fof(f7,axiom,(
% 11.79/1.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f30,plain,(
% 11.79/1.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.79/1.99    inference(nnf_transformation,[],[f7])).
% 11.79/1.99  
% 11.79/1.99  fof(f31,plain,(
% 11.79/1.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 11.79/1.99    inference(flattening,[],[f30])).
% 11.79/1.99  
% 11.79/1.99  fof(f56,plain,(
% 11.79/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f31])).
% 11.79/1.99  
% 11.79/1.99  fof(f54,plain,(
% 11.79/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f31])).
% 11.79/1.99  
% 11.79/1.99  fof(f38,plain,(
% 11.79/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f19])).
% 11.79/1.99  
% 11.79/1.99  fof(f3,axiom,(
% 11.79/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f22,plain,(
% 11.79/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.79/1.99    inference(nnf_transformation,[],[f3])).
% 11.79/1.99  
% 11.79/1.99  fof(f23,plain,(
% 11.79/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.79/1.99    inference(flattening,[],[f22])).
% 11.79/1.99  
% 11.79/1.99  fof(f43,plain,(
% 11.79/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f23])).
% 11.79/1.99  
% 11.79/1.99  fof(f63,plain,(
% 11.79/1.99    sK8 != sK10 | sK7 != sK9),
% 11.79/1.99    inference(cnf_transformation,[],[f35])).
% 11.79/1.99  
% 11.79/1.99  fof(f51,plain,(
% 11.79/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f29])).
% 11.79/1.99  
% 11.79/1.99  fof(f8,axiom,(
% 11.79/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.79/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.79/1.99  
% 11.79/1.99  fof(f32,plain,(
% 11.79/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.79/1.99    inference(nnf_transformation,[],[f8])).
% 11.79/1.99  
% 11.79/1.99  fof(f33,plain,(
% 11.79/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.79/1.99    inference(flattening,[],[f32])).
% 11.79/1.99  
% 11.79/1.99  fof(f59,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.79/1.99    inference(cnf_transformation,[],[f33])).
% 11.79/1.99  
% 11.79/1.99  fof(f71,plain,(
% 11.79/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.79/1.99    inference(equality_resolution,[],[f59])).
% 11.79/1.99  
% 11.79/1.99  fof(f62,plain,(
% 11.79/1.99    k1_xboole_0 != sK8),
% 11.79/1.99    inference(cnf_transformation,[],[f35])).
% 11.79/1.99  
% 11.79/1.99  fof(f57,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.79/1.99    inference(cnf_transformation,[],[f33])).
% 11.79/1.99  
% 11.79/1.99  fof(f58,plain,(
% 11.79/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.79/1.99    inference(cnf_transformation,[],[f33])).
% 11.79/1.99  
% 11.79/1.99  fof(f72,plain,(
% 11.79/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.79/1.99    inference(equality_resolution,[],[f58])).
% 11.79/1.99  
% 11.79/1.99  fof(f55,plain,(
% 11.79/1.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 11.79/1.99    inference(cnf_transformation,[],[f31])).
% 11.79/1.99  
% 11.79/1.99  fof(f61,plain,(
% 11.79/1.99    k1_xboole_0 != sK7),
% 11.79/1.99    inference(cnf_transformation,[],[f35])).
% 11.79/1.99  
% 11.79/1.99  fof(f46,plain,(
% 11.79/1.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.79/1.99    inference(cnf_transformation,[],[f29])).
% 11.79/1.99  
% 11.79/1.99  fof(f70,plain,(
% 11.79/1.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.79/1.99    inference(equality_resolution,[],[f46])).
% 11.79/1.99  
% 11.79/1.99  cnf(c_13,plain,
% 11.79/1.99      ( r2_hidden(sK3(X0,X1,X2),X0)
% 11.79/1.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 11.79/1.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 11.79/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_566,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,X1) = X2
% 11.79/1.99      | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
% 11.79/1.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_8,plain,
% 11.79/1.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3,plain,
% 11.79/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_574,plain,
% 11.79/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.79/1.99      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1634,plain,
% 11.79/1.99      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 11.79/1.99      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_8,c_574]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_9,plain,
% 11.79/1.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 11.79/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_51,plain,
% 11.79/1.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1658,plain,
% 11.79/1.99      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 11.79/1.99      inference(global_propositional_subsumption,[status(thm)],[c_1634,c_51]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1659,plain,
% 11.79/1.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.79/1.99      inference(renaming,[status(thm)],[c_1658]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2412,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 11.79/1.99      | r2_hidden(sK3(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_566,c_1659]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_27,negated_conjecture,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK9,sK10) ),
% 11.79/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_16,plain,
% 11.79/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK6(X1,X2,X0),X2) ),
% 11.79/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_563,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.79/1.99      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1,plain,
% 11.79/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_576,plain,
% 11.79/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.79/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_18,plain,
% 11.79/1.99      ( ~ r2_hidden(X0,X1)
% 11.79/1.99      | ~ r2_hidden(X2,X3)
% 11.79/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_565,plain,
% 11.79/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.79/1.99      | r2_hidden(X2,X3) != iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1872,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_27,c_565]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_20,plain,
% 11.79/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_560,plain,
% 11.79/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3036,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) != iProver_top
% 11.79/1.99      | r2_hidden(X0,sK7) = iProver_top
% 11.79/1.99      | r2_hidden(X1,sK10) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_1872,c_560]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_8308,plain,
% 11.79/1.99      ( r2_hidden(X0,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
% 11.79/1.99      | r1_tarski(sK9,X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_576,c_3036]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_16941,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,sK10)) != iProver_top
% 11.79/1.99      | r2_hidden(sK0(sK9,X2),sK7) = iProver_top
% 11.79/1.99      | r1_tarski(sK9,X2) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_563,c_8308]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_39285,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
% 11.79/1.99      | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
% 11.79/1.99      | r1_tarski(sK9,X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_27,c_16941]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_40533,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
% 11.79/1.99      | r2_hidden(sK0(sK9,X1),sK7) = iProver_top
% 11.79/1.99      | r1_tarski(sK9,X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_2412,c_39285]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_0,plain,
% 11.79/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_577,plain,
% 11.79/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.79/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_40932,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
% 11.79/1.99      | r1_tarski(sK9,sK7) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_40533,c_577]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5,plain,
% 11.79/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_24,negated_conjecture,
% 11.79/1.99      ( sK7 != sK9 | sK8 != sK10 ),
% 11.79/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1063,plain,
% 11.79/1.99      ( ~ r1_tarski(sK9,sK7) | ~ r1_tarski(sK7,sK9) | sK8 != sK10 ),
% 11.79/1.99      inference(resolution,[status(thm)],[c_5,c_24]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1189,plain,
% 11.79/1.99      ( ~ r1_tarski(sK9,sK7)
% 11.79/1.99      | ~ r1_tarski(sK7,sK9)
% 11.79/1.99      | ~ r1_tarski(sK10,sK8)
% 11.79/1.99      | ~ r1_tarski(sK8,sK10) ),
% 11.79/1.99      inference(resolution,[status(thm)],[c_1063,c_5]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1190,plain,
% 11.79/1.99      ( r1_tarski(sK9,sK7) != iProver_top
% 11.79/1.99      | r1_tarski(sK7,sK9) != iProver_top
% 11.79/1.99      | r1_tarski(sK10,sK8) != iProver_top
% 11.79/1.99      | r1_tarski(sK8,sK10) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_12,plain,
% 11.79/1.99      ( r2_hidden(sK4(X0,X1,X2),X1)
% 11.79/1.99      | r2_hidden(sK2(X0,X1,X2),X2)
% 11.79/1.99      | k2_zfmisc_1(X0,X1) = X2 ),
% 11.79/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_567,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,X1) = X2
% 11.79/1.99      | r2_hidden(sK4(X0,X1,X2),X1) = iProver_top
% 11.79/1.99      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2833,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = X1
% 11.79/1.99      | r2_hidden(sK2(X0,k1_xboole_0,X1),X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_567,c_1659]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_21,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2843,plain,
% 11.79/1.99      ( k1_xboole_0 = X0 | r2_hidden(sK2(X1,k1_xboole_0,X0),X0) = iProver_top ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_2833,c_21]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_832,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) = iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_27,c_560]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2066,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) = iProver_top
% 11.79/1.99      | r2_hidden(X0,sK7) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK8) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_565,c_832]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5361,plain,
% 11.79/1.99      ( sK8 = k1_xboole_0
% 11.79/1.99      | r2_hidden(X0,sK9) = iProver_top
% 11.79/1.99      | r2_hidden(X0,sK7) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_2843,c_2066]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_25,negated_conjecture,
% 11.79/1.99      ( k1_xboole_0 != sK8 ),
% 11.79/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_23,plain,
% 11.79/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.79/1.99      | k1_xboole_0 = X1
% 11.79/1.99      | k1_xboole_0 = X0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_28,plain,
% 11.79/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.79/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_22,plain,
% 11.79/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.79/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_29,plain,
% 11.79/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_271,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_757,plain,
% 11.79/1.99      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_271]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_758,plain,
% 11.79/1.99      ( sK8 != k1_xboole_0 | k1_xboole_0 = sK8 | k1_xboole_0 != k1_xboole_0 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_757]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5669,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) = iProver_top | r2_hidden(X0,sK7) != iProver_top ),
% 11.79/1.99      inference(global_propositional_subsumption,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_5361,c_25,c_28,c_29,c_758]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5677,plain,
% 11.79/1.99      ( r2_hidden(sK0(sK7,X0),sK9) = iProver_top
% 11.79/1.99      | r1_tarski(sK7,X0) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_576,c_5669]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_6111,plain,
% 11.79/1.99      ( r1_tarski(sK7,sK9) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_5677,c_577]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_19,plain,
% 11.79/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 11.79/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_561,plain,
% 11.79/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_831,plain,
% 11.79/1.99      ( r2_hidden(X0,sK10) = iProver_top
% 11.79/1.99      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_27,c_561]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1901,plain,
% 11.79/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK10) = iProver_top
% 11.79/1.99      | r2_hidden(X1,sK8) != iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_565,c_831]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_5218,plain,
% 11.79/1.99      ( r2_hidden(X0,sK7) != iProver_top
% 11.79/1.99      | r2_hidden(sK0(sK8,X1),sK10) = iProver_top
% 11.79/1.99      | r1_tarski(sK8,X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_576,c_1901]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_15543,plain,
% 11.79/1.99      ( sK7 = k1_xboole_0
% 11.79/1.99      | r2_hidden(sK0(sK8,X0),sK10) = iProver_top
% 11.79/1.99      | r1_tarski(sK8,X0) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_2843,c_5218]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_26,negated_conjecture,
% 11.79/1.99      ( k1_xboole_0 != sK7 ),
% 11.79/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_759,plain,
% 11.79/1.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_271]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_760,plain,
% 11.79/1.99      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_759]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_15991,plain,
% 11.79/1.99      ( r2_hidden(sK0(sK8,X0),sK10) = iProver_top
% 11.79/1.99      | r1_tarski(sK8,X0) = iProver_top ),
% 11.79/1.99      inference(global_propositional_subsumption,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_15543,c_26,c_28,c_29,c_760]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_15999,plain,
% 11.79/1.99      ( r1_tarski(sK8,sK10) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_15991,c_577]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_17,plain,
% 11.79/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X1) ),
% 11.79/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_562,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.79/1.99      | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
% 11.79/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_3035,plain,
% 11.79/1.99      ( r2_hidden(X0,sK9) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK8) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_1872,c_561]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_8018,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(sK9,X1)) != iProver_top
% 11.79/1.99      | r2_hidden(X2,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(X2,sK8) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_562,c_3035]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_19881,plain,
% 11.79/1.99      ( r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK8) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_27,c_8018]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_20123,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
% 11.79/1.99      | r2_hidden(X1,sK10) != iProver_top
% 11.79/1.99      | r2_hidden(X1,sK8) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_2412,c_19881]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_20768,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
% 11.79/1.99      | r2_hidden(sK0(sK10,X1),sK8) = iProver_top
% 11.79/1.99      | r1_tarski(sK10,X1) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_576,c_20123]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_37245,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0
% 11.79/1.99      | r1_tarski(sK10,sK8) = iProver_top ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_20768,c_577]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_42084,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) = k1_xboole_0 ),
% 11.79/1.99      inference(global_propositional_subsumption,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_40932,c_1190,c_6111,c_15999,c_37245]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_42111,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 11.79/1.99      inference(superposition,[status(thm)],[c_42084,c_23]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_731,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,X0) != k1_xboole_0
% 11.79/1.99      | k1_xboole_0 = X0
% 11.79/1.99      | k1_xboole_0 = sK7 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_807,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) != k1_xboole_0
% 11.79/1.99      | k1_xboole_0 = sK7
% 11.79/1.99      | k1_xboole_0 = sK8 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_731]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_940,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) != X0
% 11.79/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.79/1.99      | k1_xboole_0 != X0 ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_271]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1421,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) != k2_zfmisc_1(sK7,sK8)
% 11.79/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.79/1.99      | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_940]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_270,plain,( X0 = X0 ),theory(equality) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_1422,plain,
% 11.79/1.99      ( k2_zfmisc_1(sK7,sK8) = k2_zfmisc_1(sK7,sK8) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_270]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_2603,plain,
% 11.79/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),X0) != k1_xboole_0
% 11.79/1.99      | k1_xboole_0 = X0
% 11.79/1.99      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 11.79/1.99      inference(instantiation,[status(thm)],[c_23]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_42637,plain,
% 11.79/1.99      ( k1_xboole_0 = X0 ),
% 11.79/1.99      inference(global_propositional_subsumption,
% 11.79/1.99                [status(thm)],
% 11.79/1.99                [c_42111,c_26,c_25,c_807,c_1190,c_1421,c_1422,c_2603,c_6111,
% 11.79/1.99                 c_15999,c_37245,c_40932]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_42787,plain,
% 11.79/1.99      ( k1_xboole_0 != k1_xboole_0 ),
% 11.79/1.99      inference(demodulation,[status(thm)],[c_42637,c_26]) ).
% 11.79/1.99  
% 11.79/1.99  cnf(c_42808,plain,
% 11.79/1.99      ( $false ),
% 11.79/1.99      inference(equality_resolution_simp,[status(thm)],[c_42787]) ).
% 11.79/1.99  
% 11.79/1.99  
% 11.79/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.79/1.99  
% 11.79/1.99  ------                               Statistics
% 11.79/1.99  
% 11.79/1.99  ------ Selected
% 11.79/1.99  
% 11.79/1.99  total_time:                             1.113
% 11.79/1.99  
%------------------------------------------------------------------------------
