%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:13 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1271)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK9 != sK12
        | sK8 != sK11
        | sK7 != sK10 )
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( sK9 != sK12
      | sK8 != sK11
      | sK7 != sK10 )
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f22,f39])).

fof(f67,plain,(
    k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK12) ),
    inference(definition_unfolding,[],[f67,f66,f66])).

fof(f70,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f34,f37,f36,f35])).

fof(f50,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f71,plain,
    ( sK9 != sK12
    | sK8 != sK11
    | sK7 != sK10 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_24,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK12) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1331,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = k2_zfmisc_1(sK10,sK11)
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29,c_24])).

cnf(c_1633,plain,
    ( k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8)
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24,c_1331])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_71,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_75,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_416,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1055,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_1056,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_4804,plain,
    ( sK12 = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_26,c_71,c_75,c_1056])).

cnf(c_4805,plain,
    ( k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8)
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4804])).

cnf(c_23,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4814,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK11
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4805,c_23])).

cnf(c_7585,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK11 = sK8
    | sK11 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4814,c_23])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1057,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_1058,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1059,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_1060,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_14086,plain,
    ( sK11 = k1_xboole_0
    | sK11 = sK8
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7585,c_28,c_27,c_71,c_75,c_1058,c_1060])).

cnf(c_14087,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK11 = sK8
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_14086])).

cnf(c_1254,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = sK12
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29,c_23])).

cnf(c_1550,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23,c_1254])).

cnf(c_1765,plain,
    ( sK12 = k1_xboole_0
    | sK12 = sK9
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_26,c_71,c_75,c_1056])).

cnf(c_1766,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1765])).

cnf(c_1777,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k1_xboole_0,sK12)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1766,c_29])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_818,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_820,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2367,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_820])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_803,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18327,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_803])).

cnf(c_43005,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0
    | sK9 = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_18327])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_77,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_821,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_806,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4607,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_820])).

cnf(c_23132,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_4607])).

cnf(c_23315,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_23132])).

cnf(c_24411,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_23315])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0,sK9)
    | ~ r1_tarski(sK9,X0)
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1270,plain,
    ( sK9 = X0
    | r1_tarski(X0,sK9) != iProver_top
    | r1_tarski(sK9,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_1272,plain,
    ( sK9 = k1_xboole_0
    | r1_tarski(sK9,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1350,plain,
    ( r1_tarski(k1_xboole_0,sK9)
    | r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1354,plain,
    ( r1_tarski(k1_xboole_0,sK9) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_4655,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4666,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4655])).

cnf(c_23316,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_23132])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_804,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24519,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | r1_tarski(sK9,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23316,c_804])).

cnf(c_24627,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | r1_tarski(sK9,k1_xboole_0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24519])).

cnf(c_27189,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24411,c_26,c_71,c_75,c_77,c_1056,c_1272,c_1354,c_4666,c_24627])).

cnf(c_27190,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
    inference(renaming,[status(thm)],[c_27189])).

cnf(c_27200,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_27190])).

cnf(c_43534,plain,
    ( sK12 = k1_xboole_0
    | sK12 = sK9
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43005,c_26,c_71,c_75,c_5,c_1056,c_1271,c_1350,c_4655,c_24165])).

cnf(c_43535,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_43534])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_802,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1539,plain,
    ( sK12 = k1_xboole_0
    | r1_tarski(sK12,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_802])).

cnf(c_43645,plain,
    ( sK12 = sK9
    | sK12 = k1_xboole_0
    | r1_tarski(sK12,k2_zfmisc_1(k1_xboole_0,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_43535,c_1539])).

cnf(c_1276,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1278,plain,
    ( ~ r1_tarski(sK8,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK8)
    | sK8 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_1364,plain,
    ( r1_tarski(k1_xboole_0,sK8)
    | r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5147,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18328,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_804])).

cnf(c_43542,plain,
    ( sK7 = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0
    | r1_tarski(sK8,X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43535,c_18328])).

cnf(c_44156,plain,
    ( r1_tarski(sK8,X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK7 = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_43542])).

cnf(c_44158,plain,
    ( r1_tarski(sK8,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK7 = k1_xboole_0
    | sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_44156])).

cnf(c_44567,plain,
    ( sK12 = k1_xboole_0
    | sK12 = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_43645,c_28,c_27,c_71,c_75,c_77,c_1058,c_1060,c_1279,c_1368,c_5158,c_44157])).

cnf(c_44568,plain,
    ( sK12 = sK9
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_44567])).

cnf(c_44598,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44568,c_29])).

cnf(c_45093,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k1_xboole_0,sK9)
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK11 = sK8
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14087,c_44598])).

cnf(c_1008,plain,
    ( ~ r1_tarski(sK8,k2_zfmisc_1(X0,sK8))
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1009,plain,
    ( k1_xboole_0 = sK8
    | r1_tarski(sK8,k2_zfmisc_1(X0,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1013,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(X0,sK7))
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1014,plain,
    ( k1_xboole_0 = sK7
    | r1_tarski(sK7,k2_zfmisc_1(X0,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_1167,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(X0,sK8))
    | r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1173,plain,
    ( r1_tarski(sK8,k2_zfmisc_1(X0,sK8)) = iProver_top
    | r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_1182,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(X0,sK7))
    | r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1188,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(X0,sK7)) = iProver_top
    | r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_1283,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1284,plain,
    ( sK7 = X0
    | r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1283])).

cnf(c_1286,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_1378,plain,
    ( r1_tarski(k1_xboole_0,sK7)
    | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1382,plain,
    ( r1_tarski(k1_xboole_0,sK7) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_2094,plain,
    ( ~ r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2103,plain,
    ( r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_2112,plain,
    ( ~ r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2121,plain,
    ( r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_5594,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5605,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5594])).

cnf(c_4813,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK10
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4805,c_24])).

cnf(c_7551,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = sK7
    | sK10 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK8 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4813,c_24])).

cnf(c_9619,plain,
    ( sK11 = k1_xboole_0
    | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = sK7
    | sK10 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7551,c_28,c_27,c_71,c_75,c_1058,c_1060])).

cnf(c_9620,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = sK7
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9619])).

cnf(c_22,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_800,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9634,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = sK7
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | v1_xboole_0(sK10) = iProver_top
    | v1_xboole_0(sK11) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9620,c_800])).

cnf(c_14101,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK11 = sK8
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | v1_xboole_0(sK10) = iProver_top
    | v1_xboole_0(sK11) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14087,c_800])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_805,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4817,plain,
    ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK12 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_805])).

cnf(c_1003,plain,
    ( ~ r1_tarski(sK9,k2_zfmisc_1(X0,sK9))
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1004,plain,
    ( k1_xboole_0 = sK9
    | r1_tarski(sK9,k2_zfmisc_1(X0,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_1137,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(X0,sK9))
    | r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1143,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(X0,sK9)) = iProver_top
    | r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_2076,plain,
    ( ~ r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9)
    | ~ v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2085,plain,
    ( r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_807,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4765,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_820])).

cnf(c_26072,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_4765])).

cnf(c_36075,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_26072])).

cnf(c_36241,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_36075])).

cnf(c_36708,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK11) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_36241,c_800])).

cnf(c_39046,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4817,c_26,c_1004,c_1143,c_2085,c_36708])).

cnf(c_39061,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK11) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_39046,c_800])).

cnf(c_25,negated_conjecture,
    ( sK7 != sK10
    | sK8 != sK11
    | sK9 != sK12 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_44597,plain,
    ( sK10 != sK7
    | sK11 != sK8
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44568,c_25])).

cnf(c_23115,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_4607])).

cnf(c_30911,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_23115])).

cnf(c_31093,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_821,c_30911])).

cnf(c_31550,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK10) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_31093,c_800])).

cnf(c_47232,plain,
    ( v1_xboole_0(sK10) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31550,c_26,c_1004,c_1143,c_2085])).

cnf(c_47233,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_47232])).

cnf(c_47248,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_47233,c_18327])).

cnf(c_47296,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(sK7,k1_xboole_0) = iProver_top
    | v1_xboole_0(sK10) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47248])).

cnf(c_48879,plain,
    ( sK10 = k1_xboole_0
    | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45093,c_28,c_27,c_71,c_75,c_77,c_1009,c_1014,c_1058,c_1060,c_1173,c_1188,c_1286,c_1382,c_2103,c_2121,c_5605,c_9634,c_14101,c_39061,c_44597,c_47296])).

cnf(c_48880,plain,
    ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_48879])).

cnf(c_49003,plain,
    ( sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | r1_tarski(sK12,k2_zfmisc_1(k1_xboole_0,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_48880,c_1539])).

cnf(c_48899,plain,
    ( sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48880,c_800])).

cnf(c_49591,plain,
    ( v1_xboole_0(sK7)
    | v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_48899])).

cnf(c_49687,plain,
    ( sK12 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK10 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49003,c_28,c_27,c_5,c_1008,c_1013,c_1167,c_1182,c_2094,c_2112,c_49591])).

cnf(c_49688,plain,
    ( sK10 = k1_xboole_0
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_49687])).

cnf(c_49722,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK11),sK12) = k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49688,c_29])).

cnf(c_47250,plain,
    ( v1_xboole_0(sK10) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_47233,c_800])).

cnf(c_48605,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47250,c_28,c_27,c_71,c_75,c_77,c_1058,c_1060,c_1286,c_1382,c_5605,c_47296])).

cnf(c_49692,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49688,c_48605])).

cnf(c_49899,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_49692])).

cnf(c_50228,plain,
    ( sK11 = k1_xboole_0
    | sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49722,c_5,c_49899])).

cnf(c_39499,plain,
    ( v1_xboole_0(sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39061,c_28,c_27,c_1009,c_1014,c_1173,c_1188,c_2103,c_2121])).

cnf(c_50240,plain,
    ( sK12 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_50228,c_39499])).

cnf(c_50438,plain,
    ( sK12 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_50240,c_77])).

cnf(c_2045,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
    | v1_xboole_0(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_805])).

cnf(c_2927,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK12) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_800])).

cnf(c_3649,plain,
    ( v1_xboole_0(sK12) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2927,c_26,c_1004,c_1143,c_2085])).

cnf(c_3650,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
    | v1_xboole_0(sK12) != iProver_top ),
    inference(renaming,[status(thm)],[c_3649])).

cnf(c_3655,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_3650,c_800])).

cnf(c_18315,plain,
    ( v1_xboole_0(sK12) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3655,c_28,c_27,c_1009,c_1014,c_1173,c_1188,c_2103,c_2121])).

cnf(c_50466,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50438,c_18315])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50466,c_77])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.41/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/1.99  
% 11.41/1.99  ------  iProver source info
% 11.41/1.99  
% 11.41/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.41/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/1.99  git: non_committed_changes: false
% 11.41/1.99  git: last_make_outside_of_git: false
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  
% 11.41/1.99  ------ Input Options
% 11.41/1.99  
% 11.41/1.99  --out_options                           all
% 11.41/1.99  --tptp_safe_out                         true
% 11.41/1.99  --problem_path                          ""
% 11.41/1.99  --include_path                          ""
% 11.41/1.99  --clausifier                            res/vclausify_rel
% 11.41/1.99  --clausifier_options                    --mode clausify
% 11.41/1.99  --stdin                                 false
% 11.41/1.99  --stats_out                             all
% 11.41/1.99  
% 11.41/1.99  ------ General Options
% 11.41/1.99  
% 11.41/1.99  --fof                                   false
% 11.41/1.99  --time_out_real                         305.
% 11.41/1.99  --time_out_virtual                      -1.
% 11.41/1.99  --symbol_type_check                     false
% 11.41/1.99  --clausify_out                          false
% 11.41/1.99  --sig_cnt_out                           false
% 11.41/1.99  --trig_cnt_out                          false
% 11.41/1.99  --trig_cnt_out_tolerance                1.
% 11.41/1.99  --trig_cnt_out_sk_spl                   false
% 11.41/1.99  --abstr_cl_out                          false
% 11.41/1.99  
% 11.41/1.99  ------ Global Options
% 11.41/1.99  
% 11.41/1.99  --schedule                              default
% 11.41/1.99  --add_important_lit                     false
% 11.41/1.99  --prop_solver_per_cl                    1000
% 11.41/1.99  --min_unsat_core                        false
% 11.41/1.99  --soft_assumptions                      false
% 11.41/1.99  --soft_lemma_size                       3
% 11.41/1.99  --prop_impl_unit_size                   0
% 11.41/1.99  --prop_impl_unit                        []
% 11.41/1.99  --share_sel_clauses                     true
% 11.41/1.99  --reset_solvers                         false
% 11.41/1.99  --bc_imp_inh                            [conj_cone]
% 11.41/1.99  --conj_cone_tolerance                   3.
% 11.41/1.99  --extra_neg_conj                        none
% 11.41/1.99  --large_theory_mode                     true
% 11.41/1.99  --prolific_symb_bound                   200
% 11.41/1.99  --lt_threshold                          2000
% 11.41/1.99  --clause_weak_htbl                      true
% 11.41/1.99  --gc_record_bc_elim                     false
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing Options
% 11.41/1.99  
% 11.41/1.99  --preprocessing_flag                    true
% 11.41/1.99  --time_out_prep_mult                    0.1
% 11.41/1.99  --splitting_mode                        input
% 11.41/1.99  --splitting_grd                         true
% 11.41/1.99  --splitting_cvd                         false
% 11.41/1.99  --splitting_cvd_svl                     false
% 11.41/1.99  --splitting_nvd                         32
% 11.41/1.99  --sub_typing                            true
% 11.41/1.99  --prep_gs_sim                           true
% 11.41/1.99  --prep_unflatten                        true
% 11.41/1.99  --prep_res_sim                          true
% 11.41/1.99  --prep_upred                            true
% 11.41/1.99  --prep_sem_filter                       exhaustive
% 11.41/1.99  --prep_sem_filter_out                   false
% 11.41/1.99  --pred_elim                             true
% 11.41/1.99  --res_sim_input                         true
% 11.41/1.99  --eq_ax_congr_red                       true
% 11.41/1.99  --pure_diseq_elim                       true
% 11.41/1.99  --brand_transform                       false
% 11.41/1.99  --non_eq_to_eq                          false
% 11.41/1.99  --prep_def_merge                        true
% 11.41/1.99  --prep_def_merge_prop_impl              false
% 11.41/1.99  --prep_def_merge_mbd                    true
% 11.41/1.99  --prep_def_merge_tr_red                 false
% 11.41/1.99  --prep_def_merge_tr_cl                  false
% 11.41/1.99  --smt_preprocessing                     true
% 11.41/1.99  --smt_ac_axioms                         fast
% 11.41/1.99  --preprocessed_out                      false
% 11.41/1.99  --preprocessed_stats                    false
% 11.41/1.99  
% 11.41/1.99  ------ Abstraction refinement Options
% 11.41/1.99  
% 11.41/1.99  --abstr_ref                             []
% 11.41/1.99  --abstr_ref_prep                        false
% 11.41/1.99  --abstr_ref_until_sat                   false
% 11.41/1.99  --abstr_ref_sig_restrict                funpre
% 11.41/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.99  --abstr_ref_under                       []
% 11.41/1.99  
% 11.41/1.99  ------ SAT Options
% 11.41/1.99  
% 11.41/1.99  --sat_mode                              false
% 11.41/1.99  --sat_fm_restart_options                ""
% 11.41/1.99  --sat_gr_def                            false
% 11.41/1.99  --sat_epr_types                         true
% 11.41/1.99  --sat_non_cyclic_types                  false
% 11.41/1.99  --sat_finite_models                     false
% 11.41/1.99  --sat_fm_lemmas                         false
% 11.41/1.99  --sat_fm_prep                           false
% 11.41/1.99  --sat_fm_uc_incr                        true
% 11.41/1.99  --sat_out_model                         small
% 11.41/1.99  --sat_out_clauses                       false
% 11.41/1.99  
% 11.41/1.99  ------ QBF Options
% 11.41/1.99  
% 11.41/1.99  --qbf_mode                              false
% 11.41/1.99  --qbf_elim_univ                         false
% 11.41/1.99  --qbf_dom_inst                          none
% 11.41/1.99  --qbf_dom_pre_inst                      false
% 11.41/1.99  --qbf_sk_in                             false
% 11.41/1.99  --qbf_pred_elim                         true
% 11.41/1.99  --qbf_split                             512
% 11.41/1.99  
% 11.41/1.99  ------ BMC1 Options
% 11.41/1.99  
% 11.41/1.99  --bmc1_incremental                      false
% 11.41/1.99  --bmc1_axioms                           reachable_all
% 11.41/1.99  --bmc1_min_bound                        0
% 11.41/1.99  --bmc1_max_bound                        -1
% 11.41/1.99  --bmc1_max_bound_default                -1
% 11.41/1.99  --bmc1_symbol_reachability              true
% 11.41/1.99  --bmc1_property_lemmas                  false
% 11.41/1.99  --bmc1_k_induction                      false
% 11.41/1.99  --bmc1_non_equiv_states                 false
% 11.41/1.99  --bmc1_deadlock                         false
% 11.41/1.99  --bmc1_ucm                              false
% 11.41/1.99  --bmc1_add_unsat_core                   none
% 11.41/1.99  --bmc1_unsat_core_children              false
% 11.41/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.99  --bmc1_out_stat                         full
% 11.41/1.99  --bmc1_ground_init                      false
% 11.41/1.99  --bmc1_pre_inst_next_state              false
% 11.41/1.99  --bmc1_pre_inst_state                   false
% 11.41/1.99  --bmc1_pre_inst_reach_state             false
% 11.41/1.99  --bmc1_out_unsat_core                   false
% 11.41/1.99  --bmc1_aig_witness_out                  false
% 11.41/1.99  --bmc1_verbose                          false
% 11.41/1.99  --bmc1_dump_clauses_tptp                false
% 11.41/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.99  --bmc1_dump_file                        -
% 11.41/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.99  --bmc1_ucm_extend_mode                  1
% 11.41/1.99  --bmc1_ucm_init_mode                    2
% 11.41/1.99  --bmc1_ucm_cone_mode                    none
% 11.41/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.99  --bmc1_ucm_relax_model                  4
% 11.41/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.99  --bmc1_ucm_layered_model                none
% 11.41/1.99  --bmc1_ucm_max_lemma_size               10
% 11.41/1.99  
% 11.41/1.99  ------ AIG Options
% 11.41/1.99  
% 11.41/1.99  --aig_mode                              false
% 11.41/1.99  
% 11.41/1.99  ------ Instantiation Options
% 11.41/1.99  
% 11.41/1.99  --instantiation_flag                    true
% 11.41/1.99  --inst_sos_flag                         false
% 11.41/1.99  --inst_sos_phase                        true
% 11.41/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.99  --inst_lit_sel_side                     num_symb
% 11.41/1.99  --inst_solver_per_active                1400
% 11.41/1.99  --inst_solver_calls_frac                1.
% 11.41/1.99  --inst_passive_queue_type               priority_queues
% 11.41/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.99  --inst_passive_queues_freq              [25;2]
% 11.41/1.99  --inst_dismatching                      true
% 11.41/1.99  --inst_eager_unprocessed_to_passive     true
% 11.41/1.99  --inst_prop_sim_given                   true
% 11.41/1.99  --inst_prop_sim_new                     false
% 11.41/1.99  --inst_subs_new                         false
% 11.41/1.99  --inst_eq_res_simp                      false
% 11.41/1.99  --inst_subs_given                       false
% 11.41/1.99  --inst_orphan_elimination               true
% 11.41/1.99  --inst_learning_loop_flag               true
% 11.41/1.99  --inst_learning_start                   3000
% 11.41/1.99  --inst_learning_factor                  2
% 11.41/1.99  --inst_start_prop_sim_after_learn       3
% 11.41/1.99  --inst_sel_renew                        solver
% 11.41/1.99  --inst_lit_activity_flag                true
% 11.41/1.99  --inst_restr_to_given                   false
% 11.41/1.99  --inst_activity_threshold               500
% 11.41/1.99  --inst_out_proof                        true
% 11.41/1.99  
% 11.41/1.99  ------ Resolution Options
% 11.41/1.99  
% 11.41/1.99  --resolution_flag                       true
% 11.41/1.99  --res_lit_sel                           adaptive
% 11.41/1.99  --res_lit_sel_side                      none
% 11.41/1.99  --res_ordering                          kbo
% 11.41/1.99  --res_to_prop_solver                    active
% 11.41/1.99  --res_prop_simpl_new                    false
% 11.41/1.99  --res_prop_simpl_given                  true
% 11.41/1.99  --res_passive_queue_type                priority_queues
% 11.41/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.99  --res_passive_queues_freq               [15;5]
% 11.41/1.99  --res_forward_subs                      full
% 11.41/1.99  --res_backward_subs                     full
% 11.41/1.99  --res_forward_subs_resolution           true
% 11.41/1.99  --res_backward_subs_resolution          true
% 11.41/1.99  --res_orphan_elimination                true
% 11.41/1.99  --res_time_limit                        2.
% 11.41/1.99  --res_out_proof                         true
% 11.41/1.99  
% 11.41/1.99  ------ Superposition Options
% 11.41/1.99  
% 11.41/1.99  --superposition_flag                    true
% 11.41/1.99  --sup_passive_queue_type                priority_queues
% 11.41/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.99  --demod_completeness_check              fast
% 11.41/1.99  --demod_use_ground                      true
% 11.41/1.99  --sup_to_prop_solver                    passive
% 11.41/1.99  --sup_prop_simpl_new                    true
% 11.41/1.99  --sup_prop_simpl_given                  true
% 11.41/1.99  --sup_fun_splitting                     false
% 11.41/1.99  --sup_smt_interval                      50000
% 11.41/1.99  
% 11.41/1.99  ------ Superposition Simplification Setup
% 11.41/1.99  
% 11.41/1.99  --sup_indices_passive                   []
% 11.41/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_full_bw                           [BwDemod]
% 11.41/1.99  --sup_immed_triv                        [TrivRules]
% 11.41/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_immed_bw_main                     []
% 11.41/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.99  
% 11.41/1.99  ------ Combination Options
% 11.41/1.99  
% 11.41/1.99  --comb_res_mult                         3
% 11.41/1.99  --comb_sup_mult                         2
% 11.41/1.99  --comb_inst_mult                        10
% 11.41/1.99  
% 11.41/1.99  ------ Debug Options
% 11.41/1.99  
% 11.41/1.99  --dbg_backtrace                         false
% 11.41/1.99  --dbg_dump_prop_clauses                 false
% 11.41/1.99  --dbg_dump_prop_clauses_file            -
% 11.41/1.99  --dbg_out_stat                          false
% 11.41/1.99  ------ Parsing...
% 11.41/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.41/1.99  ------ Proving...
% 11.41/1.99  ------ Problem Properties 
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  clauses                                 29
% 11.41/1.99  conjectures                             5
% 11.41/1.99  EPR                                     9
% 11.41/1.99  Horn                                    19
% 11.41/1.99  unary                                   6
% 11.41/1.99  binary                                  10
% 11.41/1.99  lits                                    67
% 11.41/1.99  lits eq                                 25
% 11.41/1.99  fd_pure                                 0
% 11.41/1.99  fd_pseudo                               0
% 11.41/1.99  fd_cond                                 4
% 11.41/1.99  fd_pseudo_cond                          5
% 11.41/1.99  AC symbols                              0
% 11.41/1.99  
% 11.41/1.99  ------ Schedule dynamic 5 is on 
% 11.41/1.99  
% 11.41/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  Current options:
% 11.41/1.99  ------ 
% 11.41/1.99  
% 11.41/1.99  ------ Input Options
% 11.41/1.99  
% 11.41/1.99  --out_options                           all
% 11.41/1.99  --tptp_safe_out                         true
% 11.41/1.99  --problem_path                          ""
% 11.41/1.99  --include_path                          ""
% 11.41/1.99  --clausifier                            res/vclausify_rel
% 11.41/1.99  --clausifier_options                    --mode clausify
% 11.41/1.99  --stdin                                 false
% 11.41/1.99  --stats_out                             all
% 11.41/1.99  
% 11.41/1.99  ------ General Options
% 11.41/1.99  
% 11.41/1.99  --fof                                   false
% 11.41/1.99  --time_out_real                         305.
% 11.41/1.99  --time_out_virtual                      -1.
% 11.41/1.99  --symbol_type_check                     false
% 11.41/1.99  --clausify_out                          false
% 11.41/1.99  --sig_cnt_out                           false
% 11.41/1.99  --trig_cnt_out                          false
% 11.41/1.99  --trig_cnt_out_tolerance                1.
% 11.41/1.99  --trig_cnt_out_sk_spl                   false
% 11.41/1.99  --abstr_cl_out                          false
% 11.41/1.99  
% 11.41/1.99  ------ Global Options
% 11.41/1.99  
% 11.41/1.99  --schedule                              default
% 11.41/1.99  --add_important_lit                     false
% 11.41/1.99  --prop_solver_per_cl                    1000
% 11.41/1.99  --min_unsat_core                        false
% 11.41/1.99  --soft_assumptions                      false
% 11.41/1.99  --soft_lemma_size                       3
% 11.41/1.99  --prop_impl_unit_size                   0
% 11.41/1.99  --prop_impl_unit                        []
% 11.41/1.99  --share_sel_clauses                     true
% 11.41/1.99  --reset_solvers                         false
% 11.41/1.99  --bc_imp_inh                            [conj_cone]
% 11.41/1.99  --conj_cone_tolerance                   3.
% 11.41/1.99  --extra_neg_conj                        none
% 11.41/1.99  --large_theory_mode                     true
% 11.41/1.99  --prolific_symb_bound                   200
% 11.41/1.99  --lt_threshold                          2000
% 11.41/1.99  --clause_weak_htbl                      true
% 11.41/1.99  --gc_record_bc_elim                     false
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing Options
% 11.41/1.99  
% 11.41/1.99  --preprocessing_flag                    true
% 11.41/1.99  --time_out_prep_mult                    0.1
% 11.41/1.99  --splitting_mode                        input
% 11.41/1.99  --splitting_grd                         true
% 11.41/1.99  --splitting_cvd                         false
% 11.41/1.99  --splitting_cvd_svl                     false
% 11.41/1.99  --splitting_nvd                         32
% 11.41/1.99  --sub_typing                            true
% 11.41/1.99  --prep_gs_sim                           true
% 11.41/1.99  --prep_unflatten                        true
% 11.41/1.99  --prep_res_sim                          true
% 11.41/1.99  --prep_upred                            true
% 11.41/1.99  --prep_sem_filter                       exhaustive
% 11.41/1.99  --prep_sem_filter_out                   false
% 11.41/1.99  --pred_elim                             true
% 11.41/1.99  --res_sim_input                         true
% 11.41/1.99  --eq_ax_congr_red                       true
% 11.41/1.99  --pure_diseq_elim                       true
% 11.41/1.99  --brand_transform                       false
% 11.41/1.99  --non_eq_to_eq                          false
% 11.41/1.99  --prep_def_merge                        true
% 11.41/1.99  --prep_def_merge_prop_impl              false
% 11.41/1.99  --prep_def_merge_mbd                    true
% 11.41/1.99  --prep_def_merge_tr_red                 false
% 11.41/1.99  --prep_def_merge_tr_cl                  false
% 11.41/1.99  --smt_preprocessing                     true
% 11.41/1.99  --smt_ac_axioms                         fast
% 11.41/1.99  --preprocessed_out                      false
% 11.41/1.99  --preprocessed_stats                    false
% 11.41/1.99  
% 11.41/1.99  ------ Abstraction refinement Options
% 11.41/1.99  
% 11.41/1.99  --abstr_ref                             []
% 11.41/1.99  --abstr_ref_prep                        false
% 11.41/1.99  --abstr_ref_until_sat                   false
% 11.41/1.99  --abstr_ref_sig_restrict                funpre
% 11.41/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.99  --abstr_ref_under                       []
% 11.41/1.99  
% 11.41/1.99  ------ SAT Options
% 11.41/1.99  
% 11.41/1.99  --sat_mode                              false
% 11.41/1.99  --sat_fm_restart_options                ""
% 11.41/1.99  --sat_gr_def                            false
% 11.41/1.99  --sat_epr_types                         true
% 11.41/1.99  --sat_non_cyclic_types                  false
% 11.41/1.99  --sat_finite_models                     false
% 11.41/1.99  --sat_fm_lemmas                         false
% 11.41/1.99  --sat_fm_prep                           false
% 11.41/1.99  --sat_fm_uc_incr                        true
% 11.41/1.99  --sat_out_model                         small
% 11.41/1.99  --sat_out_clauses                       false
% 11.41/1.99  
% 11.41/1.99  ------ QBF Options
% 11.41/1.99  
% 11.41/1.99  --qbf_mode                              false
% 11.41/1.99  --qbf_elim_univ                         false
% 11.41/1.99  --qbf_dom_inst                          none
% 11.41/1.99  --qbf_dom_pre_inst                      false
% 11.41/1.99  --qbf_sk_in                             false
% 11.41/1.99  --qbf_pred_elim                         true
% 11.41/1.99  --qbf_split                             512
% 11.41/1.99  
% 11.41/1.99  ------ BMC1 Options
% 11.41/1.99  
% 11.41/1.99  --bmc1_incremental                      false
% 11.41/1.99  --bmc1_axioms                           reachable_all
% 11.41/1.99  --bmc1_min_bound                        0
% 11.41/1.99  --bmc1_max_bound                        -1
% 11.41/1.99  --bmc1_max_bound_default                -1
% 11.41/1.99  --bmc1_symbol_reachability              true
% 11.41/1.99  --bmc1_property_lemmas                  false
% 11.41/1.99  --bmc1_k_induction                      false
% 11.41/1.99  --bmc1_non_equiv_states                 false
% 11.41/1.99  --bmc1_deadlock                         false
% 11.41/1.99  --bmc1_ucm                              false
% 11.41/1.99  --bmc1_add_unsat_core                   none
% 11.41/1.99  --bmc1_unsat_core_children              false
% 11.41/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.99  --bmc1_out_stat                         full
% 11.41/1.99  --bmc1_ground_init                      false
% 11.41/1.99  --bmc1_pre_inst_next_state              false
% 11.41/1.99  --bmc1_pre_inst_state                   false
% 11.41/1.99  --bmc1_pre_inst_reach_state             false
% 11.41/1.99  --bmc1_out_unsat_core                   false
% 11.41/1.99  --bmc1_aig_witness_out                  false
% 11.41/1.99  --bmc1_verbose                          false
% 11.41/1.99  --bmc1_dump_clauses_tptp                false
% 11.41/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.99  --bmc1_dump_file                        -
% 11.41/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.99  --bmc1_ucm_extend_mode                  1
% 11.41/1.99  --bmc1_ucm_init_mode                    2
% 11.41/1.99  --bmc1_ucm_cone_mode                    none
% 11.41/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.99  --bmc1_ucm_relax_model                  4
% 11.41/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.99  --bmc1_ucm_layered_model                none
% 11.41/1.99  --bmc1_ucm_max_lemma_size               10
% 11.41/1.99  
% 11.41/1.99  ------ AIG Options
% 11.41/1.99  
% 11.41/1.99  --aig_mode                              false
% 11.41/1.99  
% 11.41/1.99  ------ Instantiation Options
% 11.41/1.99  
% 11.41/1.99  --instantiation_flag                    true
% 11.41/1.99  --inst_sos_flag                         false
% 11.41/1.99  --inst_sos_phase                        true
% 11.41/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.99  --inst_lit_sel_side                     none
% 11.41/1.99  --inst_solver_per_active                1400
% 11.41/1.99  --inst_solver_calls_frac                1.
% 11.41/1.99  --inst_passive_queue_type               priority_queues
% 11.41/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.99  --inst_passive_queues_freq              [25;2]
% 11.41/1.99  --inst_dismatching                      true
% 11.41/1.99  --inst_eager_unprocessed_to_passive     true
% 11.41/1.99  --inst_prop_sim_given                   true
% 11.41/1.99  --inst_prop_sim_new                     false
% 11.41/1.99  --inst_subs_new                         false
% 11.41/1.99  --inst_eq_res_simp                      false
% 11.41/1.99  --inst_subs_given                       false
% 11.41/1.99  --inst_orphan_elimination               true
% 11.41/1.99  --inst_learning_loop_flag               true
% 11.41/1.99  --inst_learning_start                   3000
% 11.41/1.99  --inst_learning_factor                  2
% 11.41/1.99  --inst_start_prop_sim_after_learn       3
% 11.41/1.99  --inst_sel_renew                        solver
% 11.41/1.99  --inst_lit_activity_flag                true
% 11.41/1.99  --inst_restr_to_given                   false
% 11.41/1.99  --inst_activity_threshold               500
% 11.41/1.99  --inst_out_proof                        true
% 11.41/1.99  
% 11.41/1.99  ------ Resolution Options
% 11.41/1.99  
% 11.41/1.99  --resolution_flag                       false
% 11.41/1.99  --res_lit_sel                           adaptive
% 11.41/1.99  --res_lit_sel_side                      none
% 11.41/1.99  --res_ordering                          kbo
% 11.41/1.99  --res_to_prop_solver                    active
% 11.41/1.99  --res_prop_simpl_new                    false
% 11.41/1.99  --res_prop_simpl_given                  true
% 11.41/1.99  --res_passive_queue_type                priority_queues
% 11.41/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.99  --res_passive_queues_freq               [15;5]
% 11.41/1.99  --res_forward_subs                      full
% 11.41/1.99  --res_backward_subs                     full
% 11.41/1.99  --res_forward_subs_resolution           true
% 11.41/1.99  --res_backward_subs_resolution          true
% 11.41/1.99  --res_orphan_elimination                true
% 11.41/1.99  --res_time_limit                        2.
% 11.41/1.99  --res_out_proof                         true
% 11.41/1.99  
% 11.41/1.99  ------ Superposition Options
% 11.41/1.99  
% 11.41/1.99  --superposition_flag                    true
% 11.41/1.99  --sup_passive_queue_type                priority_queues
% 11.41/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.99  --demod_completeness_check              fast
% 11.41/1.99  --demod_use_ground                      true
% 11.41/1.99  --sup_to_prop_solver                    passive
% 11.41/1.99  --sup_prop_simpl_new                    true
% 11.41/1.99  --sup_prop_simpl_given                  true
% 11.41/1.99  --sup_fun_splitting                     false
% 11.41/1.99  --sup_smt_interval                      50000
% 11.41/1.99  
% 11.41/1.99  ------ Superposition Simplification Setup
% 11.41/1.99  
% 11.41/1.99  --sup_indices_passive                   []
% 11.41/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_full_bw                           [BwDemod]
% 11.41/1.99  --sup_immed_triv                        [TrivRules]
% 11.41/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_immed_bw_main                     []
% 11.41/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.99  
% 11.41/1.99  ------ Combination Options
% 11.41/1.99  
% 11.41/1.99  --comb_res_mult                         3
% 11.41/1.99  --comb_sup_mult                         2
% 11.41/1.99  --comb_inst_mult                        10
% 11.41/1.99  
% 11.41/1.99  ------ Debug Options
% 11.41/1.99  
% 11.41/1.99  --dbg_backtrace                         false
% 11.41/1.99  --dbg_dump_prop_clauses                 false
% 11.41/1.99  --dbg_dump_prop_clauses_file            -
% 11.41/1.99  --dbg_out_stat                          false
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ Proving...
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS status Theorem for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  fof(f10,axiom,(
% 11.41/1.99    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f20,plain,(
% 11.41/1.99    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 11.41/1.99    inference(ennf_transformation,[],[f10])).
% 11.41/1.99  
% 11.41/1.99  fof(f64,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f20])).
% 11.41/1.99  
% 11.41/1.99  fof(f12,conjecture,(
% 11.41/1.99    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f13,negated_conjecture,(
% 11.41/1.99    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.41/1.99    inference(negated_conjecture,[],[f12])).
% 11.41/1.99  
% 11.41/1.99  fof(f21,plain,(
% 11.41/1.99    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 11.41/1.99    inference(ennf_transformation,[],[f13])).
% 11.41/1.99  
% 11.41/1.99  fof(f22,plain,(
% 11.41/1.99    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 11.41/1.99    inference(flattening,[],[f21])).
% 11.41/1.99  
% 11.41/1.99  fof(f39,plain,(
% 11.41/1.99    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK9 != sK12 | sK8 != sK11 | sK7 != sK10) & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f40,plain,(
% 11.41/1.99    (sK9 != sK12 | sK8 != sK11 | sK7 != sK10) & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12)),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f22,f39])).
% 11.41/1.99  
% 11.41/1.99  fof(f67,plain,(
% 11.41/1.99    k3_zfmisc_1(sK7,sK8,sK9) = k3_zfmisc_1(sK10,sK11,sK12)),
% 11.41/1.99    inference(cnf_transformation,[],[f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f11,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f66,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f11])).
% 11.41/1.99  
% 11.41/1.99  fof(f72,plain,(
% 11.41/1.99    k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK12)),
% 11.41/1.99    inference(definition_unfolding,[],[f67,f66,f66])).
% 11.41/1.99  
% 11.41/1.99  fof(f70,plain,(
% 11.41/1.99    k1_xboole_0 != sK9),
% 11.41/1.99    inference(cnf_transformation,[],[f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f4,axiom,(
% 11.41/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f31,plain,(
% 11.41/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.99    inference(nnf_transformation,[],[f4])).
% 11.41/1.99  
% 11.41/1.99  fof(f32,plain,(
% 11.41/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.99    inference(flattening,[],[f31])).
% 11.41/1.99  
% 11.41/1.99  fof(f47,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.41/1.99    inference(cnf_transformation,[],[f32])).
% 11.41/1.99  
% 11.41/1.99  fof(f74,plain,(
% 11.41/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.41/1.99    inference(equality_resolution,[],[f47])).
% 11.41/1.99  
% 11.41/1.99  fof(f49,plain,(
% 11.41/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f32])).
% 11.41/1.99  
% 11.41/1.99  fof(f65,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f20])).
% 11.41/1.99  
% 11.41/1.99  fof(f68,plain,(
% 11.41/1.99    k1_xboole_0 != sK7),
% 11.41/1.99    inference(cnf_transformation,[],[f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f69,plain,(
% 11.41/1.99    k1_xboole_0 != sK8),
% 11.41/1.99    inference(cnf_transformation,[],[f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f2,axiom,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f14,plain,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.41/1.99    inference(ennf_transformation,[],[f2])).
% 11.41/1.99  
% 11.41/1.99  fof(f27,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(nnf_transformation,[],[f14])).
% 11.41/1.99  
% 11.41/1.99  fof(f28,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(rectify,[],[f27])).
% 11.41/1.99  
% 11.41/1.99  fof(f29,plain,(
% 11.41/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f30,plain,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 11.41/1.99  
% 11.41/1.99  fof(f44,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f30])).
% 11.41/1.99  
% 11.41/1.99  fof(f1,axiom,(
% 11.41/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f23,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(nnf_transformation,[],[f1])).
% 11.41/1.99  
% 11.41/1.99  fof(f24,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(rectify,[],[f23])).
% 11.41/1.99  
% 11.41/1.99  fof(f25,plain,(
% 11.41/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f26,plain,(
% 11.41/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 11.41/1.99  
% 11.41/1.99  fof(f41,plain,(
% 11.41/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f26])).
% 11.41/1.99  
% 11.41/1.99  fof(f7,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f16,plain,(
% 11.41/1.99    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 11.41/1.99    inference(ennf_transformation,[],[f7])).
% 11.41/1.99  
% 11.41/1.99  fof(f59,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f16])).
% 11.41/1.99  
% 11.41/1.99  fof(f3,axiom,(
% 11.41/1.99    v1_xboole_0(k1_xboole_0)),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f46,plain,(
% 11.41/1.99    v1_xboole_0(k1_xboole_0)),
% 11.41/1.99    inference(cnf_transformation,[],[f3])).
% 11.41/1.99  
% 11.41/1.99  fof(f42,plain,(
% 11.41/1.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f26])).
% 11.41/1.99  
% 11.41/1.99  fof(f5,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f33,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.41/1.99    inference(nnf_transformation,[],[f5])).
% 11.41/1.99  
% 11.41/1.99  fof(f34,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.41/1.99    inference(rectify,[],[f33])).
% 11.41/1.99  
% 11.41/1.99  fof(f37,plain,(
% 11.41/1.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f36,plain,(
% 11.41/1.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f35,plain,(
% 11.41/1.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f38,plain,(
% 11.41/1.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f34,f37,f36,f35])).
% 11.41/1.99  
% 11.41/1.99  fof(f50,plain,(
% 11.41/1.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.41/1.99    inference(cnf_transformation,[],[f38])).
% 11.41/1.99  
% 11.41/1.99  fof(f79,plain,(
% 11.41/1.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.41/1.99    inference(equality_resolution,[],[f50])).
% 11.41/1.99  
% 11.41/1.99  fof(f60,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f16])).
% 11.41/1.99  
% 11.41/1.99  fof(f8,axiom,(
% 11.41/1.99    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f17,plain,(
% 11.41/1.99    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 11.41/1.99    inference(ennf_transformation,[],[f8])).
% 11.41/1.99  
% 11.41/1.99  fof(f62,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 11.41/1.99    inference(cnf_transformation,[],[f17])).
% 11.41/1.99  
% 11.41/1.99  fof(f9,axiom,(
% 11.41/1.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f18,plain,(
% 11.41/1.99    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.41/1.99    inference(ennf_transformation,[],[f9])).
% 11.41/1.99  
% 11.41/1.99  fof(f19,plain,(
% 11.41/1.99    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.41/1.99    inference(flattening,[],[f18])).
% 11.41/1.99  
% 11.41/1.99  fof(f63,plain,(
% 11.41/1.99    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f19])).
% 11.41/1.99  
% 11.41/1.99  fof(f6,axiom,(
% 11.41/1.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 11.41/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f15,plain,(
% 11.41/1.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f6])).
% 11.41/1.99  
% 11.41/1.99  fof(f58,plain,(
% 11.41/1.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f15])).
% 11.41/1.99  
% 11.41/1.99  fof(f51,plain,(
% 11.41/1.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 11.41/1.99    inference(cnf_transformation,[],[f38])).
% 11.41/1.99  
% 11.41/1.99  fof(f78,plain,(
% 11.41/1.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 11.41/1.99    inference(equality_resolution,[],[f51])).
% 11.41/1.99  
% 11.41/1.99  fof(f71,plain,(
% 11.41/1.99    sK9 != sK12 | sK8 != sK11 | sK7 != sK10),
% 11.41/1.99    inference(cnf_transformation,[],[f40])).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24,plain,
% 11.41/1.99      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 11.41/1.99      | k1_xboole_0 = X0
% 11.41/1.99      | k1_xboole_0 = X1 ),
% 11.41/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_29,negated_conjecture,
% 11.41/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK12) ),
% 11.41/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1331,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = k2_zfmisc_1(sK10,sK11)
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_29,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1633,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8)
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | sK9 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_24,c_1331]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_26,negated_conjecture,
% 11.41/1.99      ( k1_xboole_0 != sK9 ),
% 11.41/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8,plain,
% 11.41/1.99      ( r1_tarski(X0,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_71,plain,
% 11.41/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_6,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_75,plain,
% 11.41/1.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.41/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_416,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1055,plain,
% 11.41/1.99      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_416]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1056,plain,
% 11.41/1.99      ( sK9 != k1_xboole_0
% 11.41/1.99      | k1_xboole_0 = sK9
% 11.41/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1055]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4804,plain,
% 11.41/1.99      ( sK12 = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_1633,c_26,c_71,c_75,c_1056]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4805,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k2_zfmisc_1(sK7,sK8)
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_4804]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_23,plain,
% 11.41/1.99      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 11.41/1.99      | k1_xboole_0 = X0
% 11.41/1.99      | k1_xboole_0 = X1 ),
% 11.41/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4814,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | k2_relat_1(k2_zfmisc_1(sK7,sK8)) = sK11
% 11.41/1.99      | sK10 = k1_xboole_0
% 11.41/1.99      | sK11 = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_4805,c_23]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7585,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK10 = k1_xboole_0
% 11.41/1.99      | sK7 = k1_xboole_0
% 11.41/1.99      | sK11 = sK8
% 11.41/1.99      | sK11 = k1_xboole_0
% 11.41/1.99      | sK8 = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_4814,c_23]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_28,negated_conjecture,
% 11.41/1.99      ( k1_xboole_0 != sK7 ),
% 11.41/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27,negated_conjecture,
% 11.41/1.99      ( k1_xboole_0 != sK8 ),
% 11.41/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1057,plain,
% 11.41/1.99      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_416]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1058,plain,
% 11.41/1.99      ( sK8 != k1_xboole_0
% 11.41/1.99      | k1_xboole_0 = sK8
% 11.41/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1057]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1059,plain,
% 11.41/1.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_416]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1060,plain,
% 11.41/1.99      ( sK7 != k1_xboole_0
% 11.41/1.99      | k1_xboole_0 = sK7
% 11.41/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1059]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_14086,plain,
% 11.41/1.99      ( sK11 = k1_xboole_0
% 11.41/1.99      | sK11 = sK8
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK10 = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_7585,c_28,c_27,c_71,c_75,c_1058,c_1060]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_14087,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK10 = k1_xboole_0
% 11.41/1.99      | sK11 = sK8
% 11.41/1.99      | sK11 = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_14086]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1254,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = sK12
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_29,c_23]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1550,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | sK9 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_23,c_1254]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1765,plain,
% 11.41/1.99      ( sK12 = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_1550,c_26,c_71,c_75,c_1056]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1766,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_1765]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1777,plain,
% 11.41/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k1_xboole_0,sK12)
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1766,c_29]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_3,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_818,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.41/1.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_820,plain,
% 11.41/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.41/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2367,plain,
% 11.41/1.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_818,c_820]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19,plain,
% 11.41/1.99      ( r1_tarski(X0,X1)
% 11.41/1.99      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
% 11.41/1.99      | k1_xboole_0 = X2 ),
% 11.41/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_803,plain,
% 11.41/1.99      ( k1_xboole_0 = X0
% 11.41/1.99      | r1_tarski(X1,X2) = iProver_top
% 11.41/1.99      | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18327,plain,
% 11.41/1.99      ( k1_xboole_0 = X0
% 11.41/1.99      | r1_tarski(X1,X2) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_2367,c_803]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_43005,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | sK9 = k1_xboole_0
% 11.41/1.99      | r1_tarski(k2_zfmisc_1(sK7,sK8),X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK12)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1777,c_18327]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_5,plain,
% 11.41/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_77,plain,
% 11.41/1.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_0,plain,
% 11.41/1.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_821,plain,
% 11.41/1.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(X0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_16,plain,
% 11.41/1.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 11.41/1.99      | r2_hidden(sK5(X1,X2,X0),X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_806,plain,
% 11.41/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/1.99      | r2_hidden(sK5(X1,X2,X0),X1) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4607,plain,
% 11.41/1.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_806,c_820]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_23132,plain,
% 11.41/1.99      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_29,c_4607]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_23315,plain,
% 11.41/1.99      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_821,c_23132]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24411,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK12)) = iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1777,c_23315]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1269,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,sK9) | ~ r1_tarski(sK9,X0) | sK9 = X0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1270,plain,
% 11.41/1.99      ( sK9 = X0
% 11.41/1.99      | r1_tarski(X0,sK9) != iProver_top
% 11.41/1.99      | r1_tarski(sK9,X0) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1272,plain,
% 11.41/1.99      ( sK9 = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK9,k1_xboole_0) != iProver_top
% 11.41/1.99      | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1270]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1350,plain,
% 11.41/1.99      ( r1_tarski(k1_xboole_0,sK9)
% 11.41/1.99      | r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1354,plain,
% 11.41/1.99      ( r1_tarski(k1_xboole_0,sK9) = iProver_top
% 11.41/1.99      | r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4655,plain,
% 11.41/1.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0)
% 11.41/1.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4666,plain,
% 11.41/1.99      ( r2_hidden(sK1(k1_xboole_0,sK9),k1_xboole_0) != iProver_top
% 11.41/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_4655]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_23316,plain,
% 11.41/1.99      ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9),X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_818,c_23132]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18,plain,
% 11.41/1.99      ( r1_tarski(X0,X1)
% 11.41/1.99      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
% 11.41/1.99      | k1_xboole_0 = X2 ),
% 11.41/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_804,plain,
% 11.41/1.99      ( k1_xboole_0 = X0
% 11.41/1.99      | r1_tarski(X1,X2) = iProver_top
% 11.41/1.99      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24519,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK9,X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_23316,c_804]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_24627,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK9,k1_xboole_0) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_24519]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27189,plain,
% 11.41/1.99      ( v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_24411,c_26,c_71,c_75,c_77,c_1056,c_1272,c_1354,c_4666,
% 11.41/1.99                 c_24627]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27190,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(sK10,sK11)) != iProver_top ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_27189]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27200,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1766,c_27190]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_43534,plain,
% 11.41/1.99      ( sK12 = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_43005,c_26,c_71,c_75,c_5,c_1056,c_1271,c_1350,c_4655,
% 11.41/1.99                 c_24165]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_43535,plain,
% 11.41/1.99      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_43534]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_20,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_802,plain,
% 11.41/1.99      ( k1_xboole_0 = X0
% 11.41/1.99      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1539,plain,
% 11.41/1.99      ( sK12 = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK12,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_29,c_802]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_43645,plain,
% 11.41/1.99      ( sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK12,k2_zfmisc_1(k1_xboole_0,sK9)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_43535,c_1539]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1276,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | sK8 = X0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1278,plain,
% 11.41/1.99      ( ~ r1_tarski(sK8,k1_xboole_0)
% 11.41/1.99      | ~ r1_tarski(k1_xboole_0,sK8)
% 11.41/1.99      | sK8 = k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1276]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1364,plain,
% 11.41/1.99      ( r1_tarski(k1_xboole_0,sK8)
% 11.41/1.99      | r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_5147,plain,
% 11.41/1.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK8),k1_xboole_0)
% 11.41/1.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18328,plain,
% 11.41/1.99      ( k1_xboole_0 = X0
% 11.41/1.99      | r1_tarski(X1,X2) = iProver_top
% 11.41/1.99      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_2367,c_804]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_43542,plain,
% 11.41/1.99      ( sK7 = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0
% 11.41/1.99      | r1_tarski(sK8,X0) = iProver_top
% 11.41/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_43535,c_18328]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44156,plain,
% 11.41/1.99      ( r1_tarski(sK8,X0)
% 11.41/1.99      | ~ v1_xboole_0(k1_xboole_0)
% 11.41/1.99      | sK7 = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_43542]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44158,plain,
% 11.41/1.99      ( r1_tarski(sK8,k1_xboole_0)
% 11.41/1.99      | ~ v1_xboole_0(k1_xboole_0)
% 11.41/1.99      | sK7 = k1_xboole_0
% 11.41/1.99      | sK12 = sK9
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_44156]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44567,plain,
% 11.41/1.99      ( sK12 = k1_xboole_0 | sK12 = sK9 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_43645,c_28,c_27,c_71,c_75,c_77,c_1058,c_1060,c_1279,
% 11.41/1.99                 c_1368,c_5158,c_44157]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44568,plain,
% 11.41/1.99      ( sK12 = sK9 | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_44567]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44598,plain,
% 11.41/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK10,sK11),sK9) = k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_44568,c_29]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_45093,plain,
% 11.41/1.99      ( k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9) = k2_zfmisc_1(k1_xboole_0,sK9)
% 11.41/1.99      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/1.99      | sK10 = k1_xboole_0
% 11.41/1.99      | sK11 = sK8
% 11.41/1.99      | sK11 = k1_xboole_0
% 11.41/1.99      | sK12 = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_14087,c_44598]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1008,plain,
% 11.41/1.99      ( ~ r1_tarski(sK8,k2_zfmisc_1(X0,sK8)) | k1_xboole_0 = sK8 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1009,plain,
% 11.41/1.99      ( k1_xboole_0 = sK8
% 11.41/1.99      | r1_tarski(sK8,k2_zfmisc_1(X0,sK8)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1013,plain,
% 11.41/1.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(X0,sK7)) | k1_xboole_0 = sK7 ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1014,plain,
% 11.41/1.99      ( k1_xboole_0 = sK7
% 11.41/1.99      | r1_tarski(sK7,k2_zfmisc_1(X0,sK7)) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1167,plain,
% 11.41/1.99      ( r1_tarski(sK8,k2_zfmisc_1(X0,sK8))
% 11.41/1.99      | r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1173,plain,
% 11.41/2.00      ( r1_tarski(sK8,k2_zfmisc_1(X0,sK8)) = iProver_top
% 11.41/2.00      | r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1182,plain,
% 11.41/2.00      ( r1_tarski(sK7,k2_zfmisc_1(X0,sK7))
% 11.41/2.00      | r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1188,plain,
% 11.41/2.00      ( r1_tarski(sK7,k2_zfmisc_1(X0,sK7)) = iProver_top
% 11.41/2.00      | r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1283,plain,
% 11.41/2.00      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1284,plain,
% 11.41/2.00      ( sK7 = X0
% 11.41/2.00      | r1_tarski(X0,sK7) != iProver_top
% 11.41/2.00      | r1_tarski(sK7,X0) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1283]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1286,plain,
% 11.41/2.00      ( sK7 = k1_xboole_0
% 11.41/2.00      | r1_tarski(sK7,k1_xboole_0) != iProver_top
% 11.41/2.00      | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_1284]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1378,plain,
% 11.41/2.00      ( r1_tarski(k1_xboole_0,sK7)
% 11.41/2.00      | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1382,plain,
% 11.41/2.00      ( r1_tarski(k1_xboole_0,sK7) = iProver_top
% 11.41/2.00      | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2094,plain,
% 11.41/2.00      ( ~ r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8)
% 11.41/2.00      | ~ v1_xboole_0(sK8) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2103,plain,
% 11.41/2.00      ( r2_hidden(sK1(sK8,k2_zfmisc_1(X0,sK8)),sK8) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK8) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2112,plain,
% 11.41/2.00      ( ~ r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7)
% 11.41/2.00      | ~ v1_xboole_0(sK7) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2121,plain,
% 11.41/2.00      ( r2_hidden(sK1(sK7,k2_zfmisc_1(X0,sK7)),sK7) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK7) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_5594,plain,
% 11.41/2.00      ( ~ r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0)
% 11.41/2.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_5605,plain,
% 11.41/2.00      ( r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) != iProver_top
% 11.41/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_5594]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_4813,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | k1_relat_1(k2_zfmisc_1(sK7,sK8)) = sK10
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_4805,c_24]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_7551,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = sK7
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK7 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK8 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_4813,c_24]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_9619,plain,
% 11.41/2.00      ( sK11 = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = sK7
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_7551,c_28,c_27,c_71,c_75,c_1058,c_1060]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_9620,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = sK7
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(renaming,[status(thm)],[c_9619]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_22,plain,
% 11.41/2.00      ( v1_xboole_0(X0)
% 11.41/2.00      | v1_xboole_0(X1)
% 11.41/2.00      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 11.41/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_800,plain,
% 11.41/2.00      ( v1_xboole_0(X0) = iProver_top
% 11.41/2.00      | v1_xboole_0(X1) = iProver_top
% 11.41/2.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_9634,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = sK7
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | v1_xboole_0(sK10) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) = iProver_top
% 11.41/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_9620,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_14101,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = sK8
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | v1_xboole_0(sK10) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) = iProver_top
% 11.41/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_14087,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_17,plain,
% 11.41/2.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 11.41/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_805,plain,
% 11.41/2.00      ( v1_xboole_0(X0) != iProver_top
% 11.41/2.00      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_4817,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK10,sK11) = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_4805,c_805]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1003,plain,
% 11.41/2.00      ( ~ r1_tarski(sK9,k2_zfmisc_1(X0,sK9)) | k1_xboole_0 = sK9 ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_20]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1004,plain,
% 11.41/2.00      ( k1_xboole_0 = sK9
% 11.41/2.00      | r1_tarski(sK9,k2_zfmisc_1(X0,sK9)) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1003]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1137,plain,
% 11.41/2.00      ( r1_tarski(sK9,k2_zfmisc_1(X0,sK9))
% 11.41/2.00      | r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_1143,plain,
% 11.41/2.00      ( r1_tarski(sK9,k2_zfmisc_1(X0,sK9)) = iProver_top
% 11.41/2.00      | r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2076,plain,
% 11.41/2.00      ( ~ r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9)
% 11.41/2.00      | ~ v1_xboole_0(sK9) ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2085,plain,
% 11.41/2.00      ( r2_hidden(sK1(sK9,k2_zfmisc_1(X0,sK9)),sK9) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK9) != iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_15,plain,
% 11.41/2.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 11.41/2.00      | r2_hidden(sK6(X1,X2,X0),X2) ),
% 11.41/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_807,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/2.00      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 11.41/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_4765,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.41/2.00      | v1_xboole_0(X2) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_807,c_820]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_26072,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 11.41/2.00      | v1_xboole_0(X2) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_806,c_4765]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_36075,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_29,c_26072]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_36241,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_821,c_36075]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_36708,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK9) = iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_36241,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_39046,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_4817,c_26,c_1004,c_1143,c_2085,c_36708]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_39061,plain,
% 11.41/2.00      ( v1_xboole_0(sK7) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK11) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK8) = iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_39046,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_25,negated_conjecture,
% 11.41/2.00      ( sK7 != sK10 | sK8 != sK11 | sK9 != sK12 ),
% 11.41/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_44597,plain,
% 11.41/2.00      ( sK10 != sK7 | sK11 != sK8 | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_44568,c_25]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_23115,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 11.41/2.00      | v1_xboole_0(X1) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_806,c_4607]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_30911,plain,
% 11.41/2.00      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_29,c_23115]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_31093,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_821,c_30911]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_31550,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK9) = iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_31093,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_47232,plain,
% 11.41/2.00      ( v1_xboole_0(sK10) != iProver_top
% 11.41/2.00      | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_31550,c_26,c_1004,c_1143,c_2085]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_47233,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(renaming,[status(thm)],[c_47232]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_47248,plain,
% 11.41/2.00      ( sK8 = k1_xboole_0
% 11.41/2.00      | r1_tarski(sK7,X0) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_47233,c_18327]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_47296,plain,
% 11.41/2.00      ( sK8 = k1_xboole_0
% 11.41/2.00      | r1_tarski(sK7,k1_xboole_0) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(instantiation,[status(thm)],[c_47248]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_48879,plain,
% 11.41/2.00      ( sK10 = k1_xboole_0
% 11.41/2.00      | k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_45093,c_28,c_27,c_71,c_75,c_77,c_1009,c_1014,c_1058,
% 11.41/2.00                 c_1060,c_1173,c_1188,c_1286,c_1382,c_2103,c_2121,c_5605,
% 11.41/2.00                 c_9634,c_14101,c_39061,c_44597,c_47296]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_48880,plain,
% 11.41/2.00      ( k2_zfmisc_1(sK7,sK8) = k1_xboole_0
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(renaming,[status(thm)],[c_48879]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49003,plain,
% 11.41/2.00      ( sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | r1_tarski(sK12,k2_zfmisc_1(k1_xboole_0,sK9)) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_48880,c_1539]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_48899,plain,
% 11.41/2.00      ( sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | v1_xboole_0(sK7) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK8) = iProver_top
% 11.41/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_48880,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49591,plain,
% 11.41/2.00      ( v1_xboole_0(sK7)
% 11.41/2.00      | v1_xboole_0(sK8)
% 11.41/2.00      | ~ v1_xboole_0(k1_xboole_0)
% 11.41/2.00      | sK10 = k1_xboole_0
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_48899]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49687,plain,
% 11.41/2.00      ( sK12 = k1_xboole_0 | sK11 = k1_xboole_0 | sK10 = k1_xboole_0 ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_49003,c_28,c_27,c_5,c_1008,c_1013,c_1167,c_1182,
% 11.41/2.00                 c_2094,c_2112,c_49591]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49688,plain,
% 11.41/2.00      ( sK10 = k1_xboole_0 | sK11 = k1_xboole_0 | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(renaming,[status(thm)],[c_49687]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49722,plain,
% 11.41/2.00      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK11),sK12) = k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_49688,c_29]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_47250,plain,
% 11.41/2.00      ( v1_xboole_0(sK10) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK7) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK8) = iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_47233,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_48605,plain,
% 11.41/2.00      ( v1_xboole_0(sK10) != iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_47250,c_28,c_27,c_71,c_75,c_77,c_1058,c_1060,c_1286,
% 11.41/2.00                 c_1382,c_5605,c_47296]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49692,plain,
% 11.41/2.00      ( sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0
% 11.41/2.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_49688,c_48605]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_49899,plain,
% 11.41/2.00      ( ~ v1_xboole_0(k1_xboole_0)
% 11.41/2.00      | sK11 = k1_xboole_0
% 11.41/2.00      | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_49692]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_50228,plain,
% 11.41/2.00      ( sK11 = k1_xboole_0 | sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_49722,c_5,c_49899]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_39499,plain,
% 11.41/2.00      ( v1_xboole_0(sK11) != iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_39061,c_28,c_27,c_1009,c_1014,c_1173,c_1188,c_2103,
% 11.41/2.00                 c_2121]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_50240,plain,
% 11.41/2.00      ( sK12 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_50228,c_39499]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_50438,plain,
% 11.41/2.00      ( sK12 = k1_xboole_0 ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_50240,c_77]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2045,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),sK9)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK12) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_29,c_805]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_2927,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK12) != iProver_top
% 11.41/2.00      | v1_xboole_0(sK9) = iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_2045,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_3649,plain,
% 11.41/2.00      ( v1_xboole_0(sK12) != iProver_top
% 11.41/2.00      | v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_2927,c_26,c_1004,c_1143,c_2085]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_3650,plain,
% 11.41/2.00      ( v1_xboole_0(k2_zfmisc_1(sK7,sK8)) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK12) != iProver_top ),
% 11.41/2.00      inference(renaming,[status(thm)],[c_3649]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_3655,plain,
% 11.41/2.00      ( v1_xboole_0(sK7) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK8) = iProver_top
% 11.41/2.00      | v1_xboole_0(sK12) != iProver_top ),
% 11.41/2.00      inference(superposition,[status(thm)],[c_3650,c_800]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_18315,plain,
% 11.41/2.00      ( v1_xboole_0(sK12) != iProver_top ),
% 11.41/2.00      inference(global_propositional_subsumption,
% 11.41/2.00                [status(thm)],
% 11.41/2.00                [c_3655,c_28,c_27,c_1009,c_1014,c_1173,c_1188,c_2103,
% 11.41/2.00                 c_2121]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(c_50466,plain,
% 11.41/2.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.41/2.00      inference(demodulation,[status(thm)],[c_50438,c_18315]) ).
% 11.41/2.00  
% 11.41/2.00  cnf(contradiction,plain,
% 11.41/2.00      ( $false ),
% 11.41/2.00      inference(minisat,[status(thm)],[c_50466,c_77]) ).
% 11.41/2.00  
% 11.41/2.00  
% 11.41/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/2.00  
% 11.41/2.00  ------                               Statistics
% 11.41/2.00  
% 11.41/2.00  ------ General
% 11.41/2.00  
% 11.41/2.00  abstr_ref_over_cycles:                  0
% 11.41/2.00  abstr_ref_under_cycles:                 0
% 11.41/2.00  gc_basic_clause_elim:                   0
% 11.41/2.00  forced_gc_time:                         0
% 11.41/2.00  parsing_time:                           0.01
% 11.41/2.00  unif_index_cands_time:                  0.
% 11.41/2.00  unif_index_add_time:                    0.
% 11.41/2.00  orderings_time:                         0.
% 11.41/2.00  out_proof_time:                         0.047
% 11.41/2.00  total_time:                             1.365
% 11.41/2.00  num_of_symbols:                         52
% 11.41/2.00  num_of_terms:                           41589
% 11.41/2.00  
% 11.41/2.00  ------ Preprocessing
% 11.41/2.00  
% 11.41/2.00  num_of_splits:                          0
% 11.41/2.00  num_of_split_atoms:                     0
% 11.41/2.00  num_of_reused_defs:                     0
% 11.41/2.00  num_eq_ax_congr_red:                    54
% 11.41/2.00  num_of_sem_filtered_clauses:            1
% 11.41/2.00  num_of_subtypes:                        0
% 11.41/2.00  monotx_restored_types:                  0
% 11.41/2.00  sat_num_of_epr_types:                   0
% 11.41/2.00  sat_num_of_non_cyclic_types:            0
% 11.41/2.00  sat_guarded_non_collapsed_types:        0
% 11.41/2.00  num_pure_diseq_elim:                    0
% 11.41/2.00  simp_replaced_by:                       0
% 11.41/2.00  res_preprocessed:                       135
% 11.41/2.00  prep_upred:                             0
% 11.41/2.00  prep_unflattend:                        0
% 11.41/2.00  smt_new_axioms:                         0
% 11.41/2.00  pred_elim_cands:                        3
% 11.41/2.00  pred_elim:                              0
% 11.41/2.00  pred_elim_cl:                           0
% 11.41/2.00  pred_elim_cycles:                       2
% 11.41/2.00  merged_defs:                            0
% 11.41/2.00  merged_defs_ncl:                        0
% 11.41/2.00  bin_hyper_res:                          0
% 11.41/2.00  prep_cycles:                            4
% 11.41/2.00  pred_elim_time:                         0.
% 11.41/2.00  splitting_time:                         0.
% 11.41/2.00  sem_filter_time:                        0.
% 11.41/2.00  monotx_time:                            0.001
% 11.41/2.00  subtype_inf_time:                       0.
% 11.41/2.00  
% 11.41/2.00  ------ Problem properties
% 11.41/2.00  
% 11.41/2.00  clauses:                                29
% 11.41/2.00  conjectures:                            5
% 11.41/2.00  epr:                                    9
% 11.41/2.00  horn:                                   19
% 11.41/2.00  ground:                                 6
% 11.41/2.00  unary:                                  6
% 11.41/2.00  binary:                                 10
% 11.41/2.00  lits:                                   67
% 11.41/2.00  lits_eq:                                25
% 11.41/2.00  fd_pure:                                0
% 11.41/2.00  fd_pseudo:                              0
% 11.41/2.00  fd_cond:                                4
% 11.41/2.00  fd_pseudo_cond:                         5
% 11.41/2.00  ac_symbols:                             0
% 11.41/2.00  
% 11.41/2.00  ------ Propositional Solver
% 11.41/2.00  
% 11.41/2.00  prop_solver_calls:                      31
% 11.41/2.00  prop_fast_solver_calls:                 2266
% 11.41/2.00  smt_solver_calls:                       0
% 11.41/2.00  smt_fast_solver_calls:                  0
% 11.41/2.00  prop_num_of_clauses:                    20658
% 11.41/2.00  prop_preprocess_simplified:             36084
% 11.41/2.00  prop_fo_subsumed:                       242
% 11.41/2.00  prop_solver_time:                       0.
% 11.41/2.00  smt_solver_time:                        0.
% 11.41/2.00  smt_fast_solver_time:                   0.
% 11.41/2.00  prop_fast_solver_time:                  0.
% 11.41/2.00  prop_unsat_core_time:                   0.003
% 11.41/2.00  
% 11.41/2.00  ------ QBF
% 11.41/2.00  
% 11.41/2.00  qbf_q_res:                              0
% 11.41/2.00  qbf_num_tautologies:                    0
% 11.41/2.00  qbf_prep_cycles:                        0
% 11.41/2.00  
% 11.41/2.00  ------ BMC1
% 11.41/2.00  
% 11.41/2.00  bmc1_current_bound:                     -1
% 11.41/2.00  bmc1_last_solved_bound:                 -1
% 11.41/2.00  bmc1_unsat_core_size:                   -1
% 11.41/2.00  bmc1_unsat_core_parents_size:           -1
% 11.41/2.00  bmc1_merge_next_fun:                    0
% 11.41/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.41/2.00  
% 11.41/2.00  ------ Instantiation
% 11.41/2.00  
% 11.41/2.00  inst_num_of_clauses:                    6572
% 11.41/2.00  inst_num_in_passive:                    4449
% 11.41/2.00  inst_num_in_active:                     915
% 11.41/2.00  inst_num_in_unprocessed:                1208
% 11.41/2.00  inst_num_of_loops:                      1120
% 11.41/2.00  inst_num_of_learning_restarts:          0
% 11.41/2.00  inst_num_moves_active_passive:          204
% 11.41/2.00  inst_lit_activity:                      0
% 11.41/2.00  inst_lit_activity_moves:                0
% 11.41/2.00  inst_num_tautologies:                   0
% 11.41/2.00  inst_num_prop_implied:                  0
% 11.41/2.00  inst_num_existing_simplified:           0
% 11.41/2.00  inst_num_eq_res_simplified:             0
% 11.41/2.00  inst_num_child_elim:                    0
% 11.41/2.00  inst_num_of_dismatching_blockings:      15
% 11.41/2.00  inst_num_of_non_proper_insts:           1679
% 11.41/2.00  inst_num_of_duplicates:                 0
% 11.41/2.00  inst_inst_num_from_inst_to_res:         0
% 11.41/2.00  inst_dismatching_checking_time:         0.
% 11.41/2.00  
% 11.41/2.00  ------ Resolution
% 11.41/2.00  
% 11.41/2.00  res_num_of_clauses:                     0
% 11.41/2.00  res_num_in_passive:                     0
% 11.41/2.00  res_num_in_active:                      0
% 11.41/2.00  res_num_of_loops:                       139
% 11.41/2.00  res_forward_subset_subsumed:            18
% 11.41/2.00  res_backward_subset_subsumed:           0
% 11.41/2.00  res_forward_subsumed:                   0
% 11.41/2.00  res_backward_subsumed:                  0
% 11.41/2.00  res_forward_subsumption_resolution:     0
% 11.41/2.00  res_backward_subsumption_resolution:    0
% 11.41/2.00  res_clause_to_clause_subsumption:       8522
% 11.41/2.00  res_orphan_elimination:                 0
% 11.41/2.00  res_tautology_del:                      1
% 11.41/2.00  res_num_eq_res_simplified:              0
% 11.41/2.00  res_num_sel_changes:                    0
% 11.41/2.00  res_moves_from_active_to_pass:          0
% 11.41/2.00  
% 11.41/2.00  ------ Superposition
% 11.41/2.00  
% 11.41/2.00  sup_time_total:                         0.
% 11.41/2.00  sup_time_generating:                    0.
% 11.41/2.00  sup_time_sim_full:                      0.
% 11.41/2.00  sup_time_sim_immed:                     0.
% 11.41/2.00  
% 11.41/2.00  sup_num_of_clauses:                     982
% 11.41/2.00  sup_num_in_active:                      123
% 11.41/2.00  sup_num_in_passive:                     859
% 11.41/2.00  sup_num_of_loops:                       223
% 11.41/2.00  sup_fw_superposition:                   1636
% 11.41/2.00  sup_bw_superposition:                   1435
% 11.41/2.00  sup_immediate_simplified:               1454
% 11.41/2.00  sup_given_eliminated:                   0
% 11.41/2.00  comparisons_done:                       0
% 11.41/2.00  comparisons_avoided:                    304
% 11.41/2.00  
% 11.41/2.00  ------ Simplifications
% 11.41/2.00  
% 11.41/2.00  
% 11.41/2.00  sim_fw_subset_subsumed:                 996
% 11.41/2.00  sim_bw_subset_subsumed:                 204
% 11.41/2.00  sim_fw_subsumed:                        357
% 11.41/2.00  sim_bw_subsumed:                        51
% 11.41/2.00  sim_fw_subsumption_res:                 3
% 11.41/2.00  sim_bw_subsumption_res:                 0
% 11.41/2.00  sim_tautology_del:                      14
% 11.41/2.00  sim_eq_tautology_del:                   65
% 11.41/2.00  sim_eq_res_simp:                        0
% 11.41/2.00  sim_fw_demodulated:                     32
% 11.41/2.00  sim_bw_demodulated:                     67
% 11.41/2.00  sim_light_normalised:                   27
% 11.41/2.00  sim_joinable_taut:                      0
% 11.41/2.00  sim_joinable_simp:                      0
% 11.41/2.00  sim_ac_normalised:                      0
% 11.41/2.00  sim_smt_subsumption:                    0
% 11.41/2.00  
%------------------------------------------------------------------------------
