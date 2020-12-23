%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:57 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 267 expanded)
%              Number of leaves         :   16 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  247 ( 872 expanded)
%              Number of equality atoms :  115 ( 438 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f186,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f21])).

% (25160)Refutation not found, incomplete strategy% (25160)------------------------------
% (25160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25160)Termination reason: Refutation not found, incomplete strategy

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

% (25160)Memory used [KB]: 1663
% (25160)Time elapsed: 0.110 s
fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

% (25160)------------------------------
% (25160)------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f97,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f63,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f56,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f77,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2))) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f55,f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f63,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X1)
                & r2_hidden(sK6(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).

fof(f27,plain,(
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
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f186,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f184,f183])).

fof(f183,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f182,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f89,f39])).

fof(f89,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f62,f82])).

fof(f62,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f182,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f33,f173])).

fof(f173,plain,(
    ! [X14,X15] :
      ( k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | k1_xboole_0 != k2_zfmisc_1(X14,X15) ) ),
    inference(resolution,[],[f158,f124])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | k1_xboole_0 != X2 ) ),
    inference(forward_demodulation,[],[f117,f40])).

fof(f117,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0)) ) ),
    inference(superposition,[],[f79,f64])).

fof(f79,plain,(
    ! [X6,X7,X5] :
      ( k4_xboole_0(X6,X7) != X6
      | ~ r2_hidden(X5,k4_xboole_0(X6,k4_xboole_0(X6,X7))) ) ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0),sK2(X1)),k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f153,f39])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK2(X2),X0),k2_zfmisc_1(X2,X1))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f34,f183])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (741736448)
% 0.14/0.37  ipcrm: permission denied for id (744357890)
% 0.14/0.38  ipcrm: permission denied for id (741769219)
% 0.14/0.38  ipcrm: permission denied for id (741801988)
% 0.14/0.38  ipcrm: permission denied for id (744390661)
% 0.14/0.38  ipcrm: permission denied for id (741867526)
% 0.14/0.38  ipcrm: permission denied for id (744423431)
% 0.14/0.38  ipcrm: permission denied for id (744456200)
% 0.14/0.38  ipcrm: permission denied for id (741933065)
% 0.14/0.38  ipcrm: permission denied for id (744488970)
% 0.14/0.39  ipcrm: permission denied for id (741998603)
% 0.14/0.39  ipcrm: permission denied for id (744521740)
% 0.14/0.39  ipcrm: permission denied for id (744554509)
% 0.14/0.39  ipcrm: permission denied for id (742096911)
% 0.14/0.40  ipcrm: permission denied for id (742129682)
% 0.14/0.40  ipcrm: permission denied for id (744685587)
% 0.14/0.40  ipcrm: permission denied for id (742195220)
% 0.14/0.40  ipcrm: permission denied for id (742227989)
% 0.14/0.40  ipcrm: permission denied for id (744751127)
% 0.14/0.40  ipcrm: permission denied for id (742293528)
% 0.14/0.41  ipcrm: permission denied for id (744816666)
% 0.14/0.41  ipcrm: permission denied for id (742359068)
% 0.14/0.41  ipcrm: permission denied for id (744882205)
% 0.21/0.41  ipcrm: permission denied for id (742457377)
% 0.21/0.42  ipcrm: permission denied for id (742522916)
% 0.21/0.42  ipcrm: permission denied for id (745111590)
% 0.21/0.42  ipcrm: permission denied for id (745144359)
% 0.21/0.42  ipcrm: permission denied for id (745177128)
% 0.21/0.43  ipcrm: permission denied for id (742785070)
% 0.21/0.43  ipcrm: permission denied for id (745373743)
% 0.21/0.43  ipcrm: permission denied for id (745406512)
% 0.21/0.43  ipcrm: permission denied for id (742817841)
% 0.21/0.44  ipcrm: permission denied for id (745537589)
% 0.21/0.44  ipcrm: permission denied for id (745570358)
% 0.21/0.44  ipcrm: permission denied for id (745603127)
% 0.21/0.44  ipcrm: permission denied for id (745635896)
% 0.21/0.44  ipcrm: permission denied for id (745668665)
% 0.21/0.45  ipcrm: permission denied for id (745701434)
% 0.21/0.45  ipcrm: permission denied for id (745734203)
% 0.21/0.45  ipcrm: permission denied for id (743014460)
% 0.21/0.45  ipcrm: permission denied for id (745766973)
% 0.21/0.45  ipcrm: permission denied for id (743047230)
% 0.21/0.45  ipcrm: permission denied for id (743079999)
% 0.21/0.46  ipcrm: permission denied for id (743145538)
% 0.21/0.46  ipcrm: permission denied for id (743178307)
% 0.21/0.46  ipcrm: permission denied for id (743211076)
% 0.21/0.46  ipcrm: permission denied for id (743243845)
% 0.21/0.46  ipcrm: permission denied for id (745865286)
% 0.21/0.46  ipcrm: permission denied for id (745930824)
% 0.21/0.46  ipcrm: permission denied for id (743309385)
% 0.21/0.47  ipcrm: permission denied for id (743342155)
% 0.21/0.47  ipcrm: permission denied for id (743374925)
% 0.21/0.47  ipcrm: permission denied for id (746094672)
% 0.21/0.47  ipcrm: permission denied for id (746127441)
% 0.21/0.48  ipcrm: permission denied for id (746258517)
% 0.21/0.48  ipcrm: permission denied for id (743538775)
% 0.21/0.48  ipcrm: permission denied for id (746324056)
% 0.21/0.48  ipcrm: permission denied for id (746356825)
% 0.21/0.49  ipcrm: permission denied for id (746422363)
% 0.21/0.49  ipcrm: permission denied for id (743637087)
% 0.21/0.49  ipcrm: permission denied for id (743669856)
% 0.21/0.50  ipcrm: permission denied for id (746586210)
% 0.21/0.50  ipcrm: permission denied for id (746618979)
% 0.21/0.50  ipcrm: permission denied for id (743768164)
% 0.21/0.50  ipcrm: permission denied for id (746651749)
% 0.21/0.51  ipcrm: permission denied for id (743899242)
% 0.21/0.51  ipcrm: permission denied for id (746815595)
% 0.21/0.51  ipcrm: permission denied for id (743932012)
% 0.21/0.51  ipcrm: permission denied for id (746848365)
% 0.21/0.51  ipcrm: permission denied for id (746881134)
% 0.21/0.51  ipcrm: permission denied for id (746946672)
% 0.21/0.51  ipcrm: permission denied for id (746979441)
% 0.21/0.52  ipcrm: permission denied for id (744030322)
% 0.21/0.52  ipcrm: permission denied for id (744063091)
% 0.21/0.52  ipcrm: permission denied for id (744095860)
% 0.21/0.52  ipcrm: permission denied for id (744128629)
% 0.21/0.52  ipcrm: permission denied for id (747012214)
% 0.21/0.52  ipcrm: permission denied for id (744161399)
% 0.21/0.52  ipcrm: permission denied for id (744194168)
% 0.21/0.53  ipcrm: permission denied for id (744226938)
% 0.21/0.53  ipcrm: permission denied for id (744259707)
% 0.21/0.53  ipcrm: permission denied for id (747077756)
% 0.21/0.53  ipcrm: permission denied for id (747110525)
% 0.21/0.53  ipcrm: permission denied for id (747176063)
% 1.25/0.71  % (25185)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.71  % (25163)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.72  % (25161)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.72  % (25188)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.72  % (25176)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.72  % (25178)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.72  % (25172)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.72  % (25190)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.72  % (25184)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.73  % (25170)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.73  % (25186)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.73  % (25166)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.73  % (25163)Refutation not found, incomplete strategy% (25163)------------------------------
% 1.58/0.73  % (25163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (25163)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.73  
% 1.58/0.73  % (25163)Memory used [KB]: 10618
% 1.58/0.73  % (25163)Time elapsed: 0.140 s
% 1.58/0.73  % (25163)------------------------------
% 1.58/0.73  % (25163)------------------------------
% 1.58/0.73  % (25165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.58/0.73  % (25170)Refutation not found, incomplete strategy% (25170)------------------------------
% 1.58/0.73  % (25170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (25170)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.73  
% 1.58/0.73  % (25170)Memory used [KB]: 10618
% 1.58/0.73  % (25170)Time elapsed: 0.107 s
% 1.58/0.73  % (25170)------------------------------
% 1.58/0.73  % (25170)------------------------------
% 1.58/0.73  % (25180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.73  % (25160)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.73  % (25166)Refutation found. Thanks to Tanya!
% 1.58/0.73  % SZS status Theorem for theBenchmark
% 1.58/0.73  % SZS output start Proof for theBenchmark
% 1.58/0.73  fof(f187,plain,(
% 1.58/0.73    $false),
% 1.58/0.73    inference(subsumption_resolution,[],[f186,f98])).
% 1.58/0.73  fof(f98,plain,(
% 1.58/0.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.58/0.73    inference(resolution,[],[f97,f39])).
% 1.58/0.73  fof(f39,plain,(
% 1.58/0.73    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.58/0.73    inference(cnf_transformation,[],[f22])).
% 1.58/0.73  fof(f22,plain,(
% 1.58/0.73    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.58/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f21])).
% 1.58/0.73  % (25160)Refutation not found, incomplete strategy% (25160)------------------------------
% 1.58/0.73  % (25160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (25160)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.73  
% 1.58/0.73  fof(f21,plain,(
% 1.58/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  % (25160)Memory used [KB]: 1663
% 1.58/0.73  % (25160)Time elapsed: 0.110 s
% 1.58/0.73  fof(f14,plain,(
% 1.58/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.58/0.73    inference(ennf_transformation,[],[f2])).
% 1.58/0.73  % (25160)------------------------------
% 1.58/0.73  % (25160)------------------------------
% 1.58/0.73  fof(f2,axiom,(
% 1.58/0.73    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.58/0.73  fof(f97,plain,(
% 1.58/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.58/0.73    inference(resolution,[],[f63,f82])).
% 1.58/0.73  fof(f82,plain,(
% 1.58/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.58/0.73    inference(forward_demodulation,[],[f81,f64])).
% 1.58/0.73  fof(f64,plain,(
% 1.58/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.58/0.73    inference(forward_demodulation,[],[f56,f40])).
% 1.58/0.73  fof(f40,plain,(
% 1.58/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.73    inference(cnf_transformation,[],[f4])).
% 1.58/0.73  fof(f4,axiom,(
% 1.58/0.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.58/0.73  fof(f56,plain,(
% 1.58/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.58/0.73    inference(definition_unfolding,[],[f41,f38])).
% 1.58/0.73  fof(f38,plain,(
% 1.58/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.73    inference(cnf_transformation,[],[f5])).
% 1.58/0.73  fof(f5,axiom,(
% 1.58/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.73  fof(f41,plain,(
% 1.58/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.58/0.73    inference(cnf_transformation,[],[f3])).
% 1.58/0.73  fof(f3,axiom,(
% 1.58/0.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.58/0.73  fof(f81,plain,(
% 1.58/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) )),
% 1.58/0.73    inference(forward_demodulation,[],[f77,f67])).
% 1.58/0.73  fof(f67,plain,(
% 1.58/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.58/0.73    inference(resolution,[],[f36,f53])).
% 1.58/0.73  fof(f53,plain,(
% 1.58/0.73    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.58/0.73    inference(cnf_transformation,[],[f6])).
% 1.58/0.73  fof(f6,axiom,(
% 1.58/0.73    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.58/0.73  fof(f36,plain,(
% 1.58/0.73    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.58/0.73    inference(cnf_transformation,[],[f20])).
% 1.58/0.73  fof(f20,plain,(
% 1.58/0.73    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.58/0.73    inference(nnf_transformation,[],[f7])).
% 1.58/0.73  fof(f7,axiom,(
% 1.58/0.73    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.58/0.73  fof(f77,plain,(
% 1.58/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2)))) )),
% 1.58/0.73    inference(resolution,[],[f57,f53])).
% 1.58/0.73  fof(f57,plain,(
% 1.58/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.58/0.73    inference(definition_unfolding,[],[f55,f38])).
% 1.58/0.73  fof(f55,plain,(
% 1.58/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.58/0.73    inference(cnf_transformation,[],[f32])).
% 1.58/0.73  fof(f32,plain,(
% 1.58/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.58/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f31])).
% 1.58/0.73  fof(f31,plain,(
% 1.58/0.73    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  fof(f15,plain,(
% 1.58/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.58/0.73    inference(ennf_transformation,[],[f12])).
% 1.58/0.73  fof(f12,plain,(
% 1.58/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.73    inference(rectify,[],[f1])).
% 1.58/0.73  fof(f1,axiom,(
% 1.58/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.58/0.73  fof(f63,plain,(
% 1.58/0.73    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.58/0.73    inference(equality_resolution,[],[f45])).
% 1.58/0.73  fof(f45,plain,(
% 1.58/0.73    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.58/0.73    inference(cnf_transformation,[],[f30])).
% 1.58/0.73  fof(f30,plain,(
% 1.58/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.58/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f26,f29,f28,f27])).
% 1.58/0.73  fof(f27,plain,(
% 1.58/0.73    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  fof(f28,plain,(
% 1.58/0.73    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  fof(f29,plain,(
% 1.58/0.73    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  fof(f26,plain,(
% 1.58/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.58/0.73    inference(rectify,[],[f25])).
% 1.58/0.73  fof(f25,plain,(
% 1.58/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.58/0.73    inference(nnf_transformation,[],[f8])).
% 1.58/0.73  fof(f8,axiom,(
% 1.58/0.73    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.58/0.73  fof(f186,plain,(
% 1.58/0.73    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.58/0.73    inference(forward_demodulation,[],[f184,f183])).
% 1.58/0.73  fof(f183,plain,(
% 1.58/0.73    k1_xboole_0 = sK0),
% 1.58/0.73    inference(subsumption_resolution,[],[f182,f90])).
% 1.58/0.73  fof(f90,plain,(
% 1.58/0.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.58/0.73    inference(resolution,[],[f89,f39])).
% 1.58/0.73  fof(f89,plain,(
% 1.58/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.58/0.73    inference(resolution,[],[f62,f82])).
% 1.58/0.73  fof(f62,plain,(
% 1.58/0.73    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.58/0.73    inference(equality_resolution,[],[f46])).
% 1.58/0.73  fof(f46,plain,(
% 1.58/0.73    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.58/0.73    inference(cnf_transformation,[],[f30])).
% 1.58/0.73  fof(f182,plain,(
% 1.58/0.73    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.58/0.73    inference(trivial_inequality_removal,[],[f181])).
% 1.58/0.73  fof(f181,plain,(
% 1.58/0.73    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.58/0.73    inference(superposition,[],[f35,f180])).
% 1.58/0.73  fof(f180,plain,(
% 1.58/0.73    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.58/0.73    inference(subsumption_resolution,[],[f33,f173])).
% 1.58/0.73  fof(f173,plain,(
% 1.58/0.73    ( ! [X14,X15] : (k1_xboole_0 = X14 | k1_xboole_0 = X15 | k1_xboole_0 != k2_zfmisc_1(X14,X15)) )),
% 1.58/0.73    inference(resolution,[],[f158,f124])).
% 1.58/0.73  fof(f124,plain,(
% 1.58/0.73    ( ! [X2,X3] : (~r2_hidden(X3,X2) | k1_xboole_0 != X2) )),
% 1.58/0.73    inference(forward_demodulation,[],[f117,f40])).
% 1.58/0.73  fof(f117,plain,(
% 1.58/0.73    ( ! [X2,X3] : (k1_xboole_0 != X2 | ~r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0))) )),
% 1.58/0.73    inference(superposition,[],[f79,f64])).
% 1.58/0.73  fof(f79,plain,(
% 1.58/0.73    ( ! [X6,X7,X5] : (k4_xboole_0(X6,X7) != X6 | ~r2_hidden(X5,k4_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 1.58/0.73    inference(resolution,[],[f57,f37])).
% 1.58/0.73  fof(f37,plain,(
% 1.58/0.73    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.58/0.73    inference(cnf_transformation,[],[f20])).
% 1.58/0.73  fof(f158,plain,(
% 1.58/0.73    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0),sK2(X1)),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.58/0.73    inference(resolution,[],[f153,f39])).
% 1.58/0.73  fof(f153,plain,(
% 1.58/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK2(X2),X0),k2_zfmisc_1(X2,X1)) | k1_xboole_0 = X2) )),
% 1.58/0.73    inference(resolution,[],[f44,f39])).
% 1.58/0.73  fof(f44,plain,(
% 1.58/0.73    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.58/0.73    inference(cnf_transformation,[],[f24])).
% 1.58/0.73  fof(f24,plain,(
% 1.58/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.58/0.73    inference(flattening,[],[f23])).
% 1.58/0.73  fof(f23,plain,(
% 1.58/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.58/0.73    inference(nnf_transformation,[],[f9])).
% 1.58/0.73  fof(f9,axiom,(
% 1.58/0.73    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.58/0.73  fof(f33,plain,(
% 1.58/0.73    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.58/0.73    inference(cnf_transformation,[],[f19])).
% 1.58/0.73  fof(f19,plain,(
% 1.58/0.73    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 1.58/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 1.58/0.73  fof(f18,plain,(
% 1.58/0.73    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.73    introduced(choice_axiom,[])).
% 1.58/0.73  fof(f17,plain,(
% 1.58/0.73    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.58/0.73    inference(flattening,[],[f16])).
% 1.58/0.73  fof(f16,plain,(
% 1.58/0.73    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.58/0.73    inference(nnf_transformation,[],[f13])).
% 1.58/0.73  fof(f13,plain,(
% 1.58/0.73    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.58/0.73    inference(ennf_transformation,[],[f11])).
% 1.58/0.73  fof(f11,negated_conjecture,(
% 1.58/0.73    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.58/0.73    inference(negated_conjecture,[],[f10])).
% 1.58/0.73  fof(f10,conjecture,(
% 1.58/0.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.58/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.58/0.73  fof(f35,plain,(
% 1.58/0.73    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.58/0.73    inference(cnf_transformation,[],[f19])).
% 1.58/0.73  fof(f184,plain,(
% 1.58/0.73    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.58/0.73    inference(subsumption_resolution,[],[f34,f183])).
% 1.58/0.73  fof(f34,plain,(
% 1.58/0.73    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.58/0.73    inference(cnf_transformation,[],[f19])).
% 1.58/0.73  % SZS output end Proof for theBenchmark
% 1.58/0.73  % (25166)------------------------------
% 1.58/0.73  % (25166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (25166)Termination reason: Refutation
% 1.58/0.73  
% 1.58/0.73  % (25166)Memory used [KB]: 6396
% 1.58/0.73  % (25166)Time elapsed: 0.143 s
% 1.58/0.73  % (25166)------------------------------
% 1.58/0.73  % (25166)------------------------------
% 1.58/0.73  % (25172)Refutation not found, incomplete strategy% (25172)------------------------------
% 1.58/0.73  % (25172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (25164)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.73  % (25187)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.73  % (25172)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.73  
% 1.58/0.73  % (25172)Memory used [KB]: 10618
% 1.58/0.73  % (25172)Time elapsed: 0.142 s
% 1.58/0.73  % (25172)------------------------------
% 1.58/0.73  % (25172)------------------------------
% 1.58/0.73  % (25169)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.74/0.74  % (25174)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.74/0.74  % (25009)Success in time 0.369 s
%------------------------------------------------------------------------------
