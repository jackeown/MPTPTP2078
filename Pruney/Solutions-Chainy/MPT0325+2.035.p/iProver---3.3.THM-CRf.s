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
% DateTime   : Thu Dec  3 11:37:51 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 302 expanded)
%              Number of clauses        :   53 ( 105 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   22
%              Number of atoms          :  342 (1107 expanded)
%              Number of equality atoms :   92 ( 291 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f43,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

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

fof(f58,plain,
    ( ~ r1_tarski(sK8,sK10)
    | ~ r1_tarski(sK7,sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_942,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_2,c_23])).

cnf(c_1083,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_16,c_942])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2326,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK10)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1083,c_15])).

cnf(c_3681,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,X2),X2)
    | k2_zfmisc_1(sK7,X1) = X2 ),
    inference(resolution,[status(thm)],[c_10,c_2326])).

cnf(c_383,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_382,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1725,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_383,c_382])).

cnf(c_4138,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,X1,X2),X2)
    | X2 = k2_zfmisc_1(sK7,X1) ),
    inference(resolution,[status(thm)],[c_3681,c_1725])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9770,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4138,c_22])).

cnf(c_385,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_18,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2144,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_385,c_18])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_735,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_744,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1868,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_744])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_49,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1876,plain,
    ( r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1868,c_49])).

cnf(c_1877,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1876])).

cnf(c_1885,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1877])).

cnf(c_2082,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_1885])).

cnf(c_2085,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2082])).

cnf(c_9510,plain,
    ( ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2144,c_2085])).

cnf(c_9511,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 != X0 ),
    inference(renaming,[status(thm)],[c_9510])).

cnf(c_1895,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1885])).

cnf(c_9514,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9511,c_1895])).

cnf(c_9853,plain,
    ( r2_hidden(X0,sK10)
    | ~ r2_hidden(X0,sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9770,c_9514])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9866,plain,
    ( ~ r2_hidden(sK0(X0,sK10),sK8)
    | r1_tarski(X0,sK10) ),
    inference(resolution,[status(thm)],[c_9853,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10300,plain,
    ( r1_tarski(sK8,sK10) ),
    inference(resolution,[status(thm)],[c_9866,c_1])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK7,sK9)
    | ~ r1_tarski(sK8,sK10) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_10305,plain,
    ( ~ r1_tarski(sK7,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10300,c_21])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1093,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_942])).

cnf(c_2335,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK8) ),
    inference(resolution,[status(thm)],[c_1093,c_15])).

cnf(c_9,plain,
    ( r2_hidden(sK4(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k2_zfmisc_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2655,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | k2_zfmisc_1(X1,sK8) = X2 ),
    inference(resolution,[status(thm)],[c_2335,c_9])).

cnf(c_3589,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(X1,sK8,X2),X2)
    | X2 = k2_zfmisc_1(X1,sK8) ),
    inference(resolution,[status(thm)],[c_2655,c_1725])).

cnf(c_8097,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3589,c_22])).

cnf(c_8176,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK0(X0,sK9),sK7)
    | r1_tarski(X0,sK9) ),
    inference(resolution,[status(thm)],[c_8097,c_0])).

cnf(c_8324,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
    | r1_tarski(sK7,sK9) ),
    inference(resolution,[status(thm)],[c_8176,c_1])).

cnf(c_10312,plain,
    ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10305,c_8324])).

cnf(c_10487,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10312,c_9514])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.98/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/1.01  
% 3.98/1.01  ------  iProver source info
% 3.98/1.01  
% 3.98/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.98/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/1.01  git: non_committed_changes: false
% 3.98/1.01  git: last_make_outside_of_git: false
% 3.98/1.01  
% 3.98/1.01  ------ 
% 3.98/1.01  ------ Parsing...
% 3.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/1.01  ------ Proving...
% 3.98/1.01  ------ Problem Properties 
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  clauses                                 23
% 3.98/1.01  conjectures                             3
% 3.98/1.01  EPR                                     3
% 3.98/1.01  Horn                                    17
% 3.98/1.01  unary                                   6
% 3.98/1.01  binary                                  10
% 3.98/1.01  lits                                    49
% 3.98/1.01  lits eq                                 14
% 3.98/1.01  fd_pure                                 0
% 3.98/1.01  fd_pseudo                               0
% 3.98/1.01  fd_cond                                 1
% 3.98/1.01  fd_pseudo_cond                          4
% 3.98/1.01  AC symbols                              0
% 3.98/1.01  
% 3.98/1.01  ------ Input Options Time Limit: Unbounded
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  ------ 
% 3.98/1.01  Current options:
% 3.98/1.01  ------ 
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  ------ Proving...
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  % SZS status Theorem for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01   Resolution empty clause
% 3.98/1.01  
% 3.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  fof(f6,axiom,(
% 3.98/1.01    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f22,plain,(
% 3.98/1.01    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.98/1.01    inference(nnf_transformation,[],[f6])).
% 3.98/1.01  
% 3.98/1.01  fof(f23,plain,(
% 3.98/1.01    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.98/1.01    inference(rectify,[],[f22])).
% 3.98/1.01  
% 3.98/1.01  fof(f26,plain,(
% 3.98/1.01    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f25,plain,(
% 3.98/1.01    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f24,plain,(
% 3.98/1.01    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f27,plain,(
% 3.98/1.01    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f26,f25,f24])).
% 3.98/1.01  
% 3.98/1.01  fof(f46,plain,(
% 3.98/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f27])).
% 3.98/1.01  
% 3.98/1.01  fof(f7,axiom,(
% 3.98/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f28,plain,(
% 3.98/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.98/1.01    inference(nnf_transformation,[],[f7])).
% 3.98/1.01  
% 3.98/1.01  fof(f29,plain,(
% 3.98/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.98/1.01    inference(flattening,[],[f28])).
% 3.98/1.01  
% 3.98/1.01  fof(f51,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f29])).
% 3.98/1.01  
% 3.98/1.01  fof(f1,axiom,(
% 3.98/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f12,plain,(
% 3.98/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.98/1.01    inference(ennf_transformation,[],[f1])).
% 3.98/1.01  
% 3.98/1.01  fof(f16,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(nnf_transformation,[],[f12])).
% 3.98/1.01  
% 3.98/1.01  fof(f17,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(rectify,[],[f16])).
% 3.98/1.01  
% 3.98/1.01  fof(f18,plain,(
% 3.98/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f19,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.98/1.01  
% 3.98/1.01  fof(f34,plain,(
% 3.98/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f19])).
% 3.98/1.01  
% 3.98/1.01  fof(f9,conjecture,(
% 3.98/1.01    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f10,negated_conjecture,(
% 3.98/1.01    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.98/1.01    inference(negated_conjecture,[],[f9])).
% 3.98/1.01  
% 3.98/1.01  fof(f14,plain,(
% 3.98/1.01    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.98/1.01    inference(ennf_transformation,[],[f10])).
% 3.98/1.01  
% 3.98/1.01  fof(f15,plain,(
% 3.98/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.98/1.01    inference(flattening,[],[f14])).
% 3.98/1.01  
% 3.98/1.01  fof(f32,plain,(
% 3.98/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f33,plain,(
% 3.98/1.01    (~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)) & k1_xboole_0 != k2_zfmisc_1(sK7,sK8) & r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f15,f32])).
% 3.98/1.01  
% 3.98/1.01  fof(f56,plain,(
% 3.98/1.01    r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10))),
% 3.98/1.01    inference(cnf_transformation,[],[f33])).
% 3.98/1.01  
% 3.98/1.01  fof(f52,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f29])).
% 3.98/1.01  
% 3.98/1.01  fof(f57,plain,(
% 3.98/1.01    k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 3.98/1.01    inference(cnf_transformation,[],[f33])).
% 3.98/1.01  
% 3.98/1.01  fof(f8,axiom,(
% 3.98/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f30,plain,(
% 3.98/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.98/1.01    inference(nnf_transformation,[],[f8])).
% 3.98/1.01  
% 3.98/1.01  fof(f31,plain,(
% 3.98/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.98/1.01    inference(flattening,[],[f30])).
% 3.98/1.01  
% 3.98/1.01  fof(f55,plain,(
% 3.98/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.98/1.01    inference(cnf_transformation,[],[f31])).
% 3.98/1.01  
% 3.98/1.01  fof(f66,plain,(
% 3.98/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.98/1.01    inference(equality_resolution,[],[f55])).
% 3.98/1.01  
% 3.98/1.01  fof(f43,plain,(
% 3.98/1.01    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 3.98/1.01    inference(cnf_transformation,[],[f27])).
% 3.98/1.01  
% 3.98/1.01  fof(f64,plain,(
% 3.98/1.01    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 3.98/1.01    inference(equality_resolution,[],[f43])).
% 3.98/1.01  
% 3.98/1.01  fof(f3,axiom,(
% 3.98/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f39,plain,(
% 3.98/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.98/1.01    inference(cnf_transformation,[],[f3])).
% 3.98/1.01  
% 3.98/1.01  fof(f2,axiom,(
% 3.98/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f11,plain,(
% 3.98/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.98/1.01    inference(rectify,[],[f2])).
% 3.98/1.01  
% 3.98/1.01  fof(f13,plain,(
% 3.98/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.98/1.01    inference(ennf_transformation,[],[f11])).
% 3.98/1.01  
% 3.98/1.01  fof(f20,plain,(
% 3.98/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f21,plain,(
% 3.98/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f20])).
% 3.98/1.01  
% 3.98/1.01  fof(f38,plain,(
% 3.98/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f21])).
% 3.98/1.01  
% 3.98/1.01  fof(f4,axiom,(
% 3.98/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f40,plain,(
% 3.98/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f4])).
% 3.98/1.01  
% 3.98/1.01  fof(f59,plain,(
% 3.98/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.98/1.01    inference(definition_unfolding,[],[f38,f40])).
% 3.98/1.01  
% 3.98/1.01  fof(f5,axiom,(
% 3.98/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f41,plain,(
% 3.98/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f5])).
% 3.98/1.01  
% 3.98/1.01  fof(f36,plain,(
% 3.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f19])).
% 3.98/1.01  
% 3.98/1.01  fof(f35,plain,(
% 3.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f19])).
% 3.98/1.01  
% 3.98/1.01  fof(f58,plain,(
% 3.98/1.01    ~r1_tarski(sK8,sK10) | ~r1_tarski(sK7,sK9)),
% 3.98/1.01    inference(cnf_transformation,[],[f33])).
% 3.98/1.01  
% 3.98/1.01  fof(f50,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f29])).
% 3.98/1.01  
% 3.98/1.01  fof(f47,plain,(
% 3.98/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f27])).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10,plain,
% 3.98/1.01      ( r2_hidden(sK3(X0,X1,X2),X0)
% 3.98/1.01      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.98/1.01      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.98/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_16,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.98/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_23,negated_conjecture,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK9,sK10)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_942,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK9,sK10))
% 3.98/1.01      | ~ r2_hidden(X0,k2_zfmisc_1(sK7,sK8)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_2,c_23]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1083,plain,
% 3.98/1.01      ( r2_hidden(X0,sK10)
% 3.98/1.01      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK7,sK8)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_16,c_942]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_15,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1)
% 3.98/1.01      | ~ r2_hidden(X2,X3)
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2326,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,sK7) | r2_hidden(X1,sK10) | ~ r2_hidden(X1,sK8) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1083,c_15]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3681,plain,
% 3.98/1.01      ( r2_hidden(X0,sK10)
% 3.98/1.01      | ~ r2_hidden(X0,sK8)
% 3.98/1.01      | r2_hidden(sK2(sK7,X1,X2),X2)
% 3.98/1.01      | k2_zfmisc_1(sK7,X1) = X2 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_10,c_2326]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_383,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_382,plain,( X0 = X0 ),theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1725,plain,
% 3.98/1.01      ( X0 != X1 | X1 = X0 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_383,c_382]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_4138,plain,
% 3.98/1.01      ( r2_hidden(X0,sK10)
% 3.98/1.01      | ~ r2_hidden(X0,sK8)
% 3.98/1.01      | r2_hidden(sK2(sK7,X1,X2),X2)
% 3.98/1.01      | X2 = k2_zfmisc_1(sK7,X1) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_3681,c_1725]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_22,negated_conjecture,
% 3.98/1.01      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
% 3.98/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9770,plain,
% 3.98/1.01      ( r2_hidden(X0,sK10)
% 3.98/1.01      | ~ r2_hidden(X0,sK8)
% 3.98/1.01      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_4138,c_22]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_385,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.98/1.01      theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_18,plain,
% 3.98/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2144,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
% 3.98/1.01      | ~ r2_hidden(X2,k1_xboole_0)
% 3.98/1.01      | X0 != X2 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_385,c_18]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_13,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK6(X1,X2,X0),X2) ),
% 3.98/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_735,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.98/1.01      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_5,plain,
% 3.98/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3,plain,
% 3.98/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.98/1.01      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.98/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_744,plain,
% 3.98/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.98/1.01      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1868,plain,
% 3.98/1.01      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 3.98/1.01      | r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_5,c_744]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_6,plain,
% 3.98/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.98/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_49,plain,
% 3.98/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1876,plain,
% 3.98/1.01      ( r2_hidden(X1,k4_xboole_0(X0,X0)) != iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1868,c_49]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1877,plain,
% 3.98/1.01      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_1876]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1885,plain,
% 3.98/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_5,c_1877]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2082,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_735,c_1885]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2085,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
% 3.98/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2082]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9510,plain,
% 3.98/1.01      ( ~ r2_hidden(X2,k1_xboole_0) | X0 != X2 ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2144,c_2085]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9511,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k1_xboole_0) | X1 != X0 ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_9510]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1895,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.98/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1885]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9514,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9511,c_1895]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9853,plain,
% 3.98/1.01      ( r2_hidden(X0,sK10) | ~ r2_hidden(X0,sK8) ),
% 3.98/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_9770,c_9514]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_0,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.98/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9866,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(X0,sK10),sK8) | r1_tarski(X0,sK10) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_9853,c_0]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.98/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10300,plain,
% 3.98/1.01      ( r1_tarski(sK8,sK10) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_9866,c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_21,negated_conjecture,
% 3.98/1.01      ( ~ r1_tarski(sK7,sK9) | ~ r1_tarski(sK8,sK10) ),
% 3.98/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10305,plain,
% 3.98/1.01      ( ~ r1_tarski(sK7,sK9) ),
% 3.98/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_10300,c_21]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_17,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1093,plain,
% 3.98/1.01      ( r2_hidden(X0,sK9)
% 3.98/1.01      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK7,sK8)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_17,c_942]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2335,plain,
% 3.98/1.01      ( r2_hidden(X0,sK9) | ~ r2_hidden(X0,sK7) | ~ r2_hidden(X1,sK8) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1093,c_15]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9,plain,
% 3.98/1.01      ( r2_hidden(sK4(X0,X1,X2),X1)
% 3.98/1.01      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.98/1.01      | k2_zfmisc_1(X0,X1) = X2 ),
% 3.98/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2655,plain,
% 3.98/1.01      ( r2_hidden(X0,sK9)
% 3.98/1.01      | ~ r2_hidden(X0,sK7)
% 3.98/1.01      | r2_hidden(sK2(X1,sK8,X2),X2)
% 3.98/1.01      | k2_zfmisc_1(X1,sK8) = X2 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_2335,c_9]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3589,plain,
% 3.98/1.01      ( r2_hidden(X0,sK9)
% 3.98/1.01      | ~ r2_hidden(X0,sK7)
% 3.98/1.01      | r2_hidden(sK2(X1,sK8,X2),X2)
% 3.98/1.01      | X2 = k2_zfmisc_1(X1,sK8) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_2655,c_1725]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_8097,plain,
% 3.98/1.01      ( r2_hidden(X0,sK9)
% 3.98/1.01      | ~ r2_hidden(X0,sK7)
% 3.98/1.01      | r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_3589,c_22]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_8176,plain,
% 3.98/1.01      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0)
% 3.98/1.01      | ~ r2_hidden(sK0(X0,sK9),sK7)
% 3.98/1.01      | r1_tarski(X0,sK9) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_8097,c_0]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_8324,plain,
% 3.98/1.01      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) | r1_tarski(sK7,sK9) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_8176,c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10312,plain,
% 3.98/1.01      ( r2_hidden(sK2(sK7,sK8,k1_xboole_0),k1_xboole_0) ),
% 3.98/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_10305,c_8324]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10487,plain,
% 3.98/1.01      ( $false ),
% 3.98/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_10312,c_9514]) ).
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  ------                               Statistics
% 3.98/1.01  
% 3.98/1.01  ------ Selected
% 3.98/1.01  
% 3.98/1.01  total_time:                             0.338
% 3.98/1.01  
%------------------------------------------------------------------------------
