%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:18 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   92 (1136 expanded)
%              Number of leaves         :   19 ( 388 expanded)
%              Depth                    :   23
%              Number of atoms          :  257 (4750 expanded)
%              Number of equality atoms :   96 (1312 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f33,f217,f110])).

fof(f110,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(k1_xboole_0,X3,X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(backward_demodulation,[],[f102,f105])).

fof(f105,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f98,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f98,plain,(
    ! [X3] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3)) ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f87,plain,(
    ! [X6,X4] : ~ r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X6)) ),
    inference(backward_demodulation,[],[f82,f86])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(resolution,[],[f80,f36])).

fof(f80,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f79,f38])).

fof(f79,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f77,f74])).

fof(f74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f73])).

fof(f73,plain,(
    k1_xboole_0 = sK8 ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f3,f31])).

fof(f31,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f24,f27,f26,f25])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X1)
        & r2_hidden(sK6(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f82,plain,(
    ! [X6,X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(k2_zfmisc_1(X5,k1_xboole_0),X6)) ),
    inference(resolution,[],[f79,f71])).

fof(f71,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,(
    ! [X4,X3] :
      ( k2_zfmisc_1(k1_xboole_0,X3) = X4
      | r2_hidden(sK3(k1_xboole_0,X3,X4),X4) ) ),
    inference(resolution,[],[f45,f91])).

fof(f91,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f88,f86])).

fof(f88,plain,(
    ! [X2,X1] : ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f81,f86])).

fof(f81,plain,(
    ! [X2,X3,X1] : ~ r2_hidden(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k1_xboole_0))) ),
    inference(resolution,[],[f79,f70])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f217,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,X1) ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f216,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1),k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f213,f86])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,k1_xboole_0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f72,f184])).

fof(f184,plain,(
    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f182,f110])).

fof(f182,plain,(
    ! [X1] : ~ r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f175,f33])).

fof(f175,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f172,f110])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f164,f37])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f160,f38])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f158,f74])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f84,f154])).

fof(f154,plain,(
    ! [X2] :
      ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f153,f91])).

fof(f153,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,sK1),k1_xboole_0)
      | ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ) ),
    inference(superposition,[],[f72,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f34,f62,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f84,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X6,X4))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f68,f37])).

fof(f68,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22365)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (22361)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (22384)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (22366)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (22377)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (22362)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22362)Refutation not found, incomplete strategy% (22362)------------------------------
% 0.21/0.52  % (22362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22362)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22362)Memory used [KB]: 1663
% 0.21/0.52  % (22362)Time elapsed: 0.113 s
% 0.21/0.52  % (22362)------------------------------
% 0.21/0.52  % (22362)------------------------------
% 0.21/0.52  % (22373)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (22373)Refutation not found, incomplete strategy% (22373)------------------------------
% 0.21/0.52  % (22373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22373)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22373)Memory used [KB]: 10618
% 0.21/0.52  % (22373)Time elapsed: 0.116 s
% 0.21/0.52  % (22373)------------------------------
% 0.21/0.52  % (22373)------------------------------
% 0.21/0.52  % (22377)Refutation not found, incomplete strategy% (22377)------------------------------
% 0.21/0.52  % (22377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22374)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (22385)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (22387)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.53  % (22369)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.53  % (22377)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (22377)Memory used [KB]: 10618
% 1.28/0.53  % (22377)Time elapsed: 0.123 s
% 1.28/0.53  % (22377)------------------------------
% 1.28/0.53  % (22377)------------------------------
% 1.28/0.53  % (22376)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.53  % (22384)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f220,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(unit_resulting_resolution,[],[f33,f217,f110])).
% 1.28/0.53  fof(f110,plain,(
% 1.28/0.53    ( ! [X4,X3] : (r2_hidden(sK3(k1_xboole_0,X3,X4),X4) | k1_xboole_0 = X4) )),
% 1.28/0.53    inference(backward_demodulation,[],[f102,f105])).
% 1.28/0.53  fof(f105,plain,(
% 1.28/0.53    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.28/0.53    inference(resolution,[],[f98,f36])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.28/0.53  fof(f98,plain,(
% 1.28/0.53    ( ! [X3] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X3))) )),
% 1.28/0.53    inference(resolution,[],[f87,f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.53    inference(rectify,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.28/0.53    inference(nnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    ( ! [X6,X4] : (~r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X6))) )),
% 1.28/0.53    inference(backward_demodulation,[],[f82,f86])).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) )),
% 1.28/0.53    inference(resolution,[],[f80,f36])).
% 1.28/0.53  fof(f80,plain,(
% 1.28/0.53    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 1.28/0.53    inference(resolution,[],[f79,f38])).
% 1.28/0.53  fof(f79,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.28/0.53    inference(resolution,[],[f77,f74])).
% 1.28/0.53  fof(f74,plain,(
% 1.28/0.53    v1_xboole_0(k1_xboole_0)),
% 1.28/0.53    inference(backward_demodulation,[],[f56,f73])).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    k1_xboole_0 = sK8),
% 1.28/0.53    inference(resolution,[],[f36,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    v1_xboole_0(sK8)),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    v1_xboole_0(sK8)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f3,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK8)),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ? [X0] : v1_xboole_0(X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.28/0.53    inference(resolution,[],[f70,f37])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f70,plain,(
% 1.28/0.53    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f42])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f24,f27,f26,f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X1) & r2_hidden(sK6(X0,X1,X8),X0)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(rectify,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(nnf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.28/0.53  fof(f82,plain,(
% 1.28/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(k2_zfmisc_1(X5,k1_xboole_0),X6))) )),
% 1.28/0.53    inference(resolution,[],[f79,f71])).
% 1.28/0.53  fof(f71,plain,(
% 1.28/0.53    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    ( ! [X4,X3] : (k2_zfmisc_1(k1_xboole_0,X3) = X4 | r2_hidden(sK3(k1_xboole_0,X3,X4),X4)) )),
% 1.28/0.53    inference(resolution,[],[f45,f91])).
% 1.28/0.53  fof(f91,plain,(
% 1.28/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f88,f86])).
% 1.28/0.53  fof(f88,plain,(
% 1.28/0.53    ( ! [X2,X1] : (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))) )),
% 1.28/0.53    inference(backward_demodulation,[],[f81,f86])).
% 1.28/0.53  fof(f81,plain,(
% 1.28/0.53    ( ! [X2,X3,X1] : (~r2_hidden(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k1_xboole_0)))) )),
% 1.28/0.53    inference(resolution,[],[f79,f70])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f217,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f216,f91])).
% 1.28/0.53  fof(f216,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK1),k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f213,f86])).
% 1.28/0.53  fof(f213,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,k1_xboole_0)) | ~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(superposition,[],[f72,f184])).
% 1.28/0.53  fof(f184,plain,(
% 1.28/0.53    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.28/0.53    inference(resolution,[],[f182,f110])).
% 1.28/0.53  fof(f182,plain,(
% 1.28/0.53    ( ! [X1] : (~r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f175,f33])).
% 1.28/0.53  fof(f175,plain,(
% 1.28/0.53    ( ! [X1] : (~r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0) )),
% 1.28/0.53    inference(resolution,[],[f172,f110])).
% 1.28/0.53  fof(f172,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f164,f37])).
% 1.28/0.53  fof(f164,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,sK0) | v1_xboole_0(sK0)) )),
% 1.28/0.53    inference(resolution,[],[f160,f38])).
% 1.28/0.53  fof(f160,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X2,sK0)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f158,f74])).
% 1.28/0.53  fof(f158,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X2,sK0)) )),
% 1.28/0.53    inference(superposition,[],[f84,f154])).
% 1.28/0.53  fof(f154,plain,(
% 1.28/0.53    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~r2_hidden(X2,sK0)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f153,f91])).
% 1.28/0.53  fof(f153,plain,(
% 1.28/0.53    ( ! [X2] : (r2_hidden(k4_tarski(X2,sK1),k1_xboole_0) | ~r2_hidden(X2,sK0) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)) )),
% 1.28/0.53    inference(superposition,[],[f72,f63])).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 1.28/0.53    inference(definition_unfolding,[],[f34,f62,f62])).
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f35,f61])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f39,f60])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f40,f59])).
% 1.28/0.53  fof(f59,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f49,f58])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f53,f57])).
% 1.28/0.53  fof(f57,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f54,f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 1.28/0.53    inference(ennf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.28/0.53    inference(negated_conjecture,[],[f13])).
% 1.28/0.53  fof(f13,conjecture,(
% 1.28/0.53    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    ( ! [X6,X4,X5,X3] : (~v1_xboole_0(k2_zfmisc_1(X6,X4)) | ~r2_hidden(X5,X6) | ~r2_hidden(X3,X4)) )),
% 1.28/0.53    inference(resolution,[],[f68,f37])).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.28/0.53    inference(equality_resolution,[],[f67])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(equality_resolution,[],[f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f72,plain,(
% 1.28/0.53    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 1.28/0.53    inference(equality_resolution,[],[f64])).
% 1.28/0.53  fof(f64,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f52,f62])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f30])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.28/0.53    inference(flattening,[],[f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.28/0.53    inference(nnf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    k1_xboole_0 != sK0),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (22384)------------------------------
% 1.28/0.53  % (22384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (22384)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (22384)Memory used [KB]: 6396
% 1.28/0.53  % (22384)Time elapsed: 0.113 s
% 1.28/0.53  % (22384)------------------------------
% 1.28/0.53  % (22384)------------------------------
% 1.28/0.53  % (22380)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.28/0.53  % (22358)Success in time 0.171 s
%------------------------------------------------------------------------------
