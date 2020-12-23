%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 686 expanded)
%              Number of leaves         :   15 ( 187 expanded)
%              Depth                    :   28
%              Number of atoms          :  306 (2279 expanded)
%              Number of equality atoms :   90 ( 439 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6719,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6626,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f6626,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f36,f6624])).

fof(f6624,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f6601,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6601,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f36,f6374])).

fof(f6374,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f6370,f6262])).

fof(f6262,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f790,f6181])).

fof(f6181,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f6180,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f6180,plain,
    ( k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f6150,f1001])).

fof(f1001,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f990,f38])).

fof(f990,plain,(
    ! [X2,X1] : k3_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f40,f821])).

fof(f821,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(resolution,[],[f791,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f791,plain,(
    ! [X8,X7] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(superposition,[],[f781,f40])).

fof(f781,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f766])).

fof(f766,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f504,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f504,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f178,f64])).

fof(f64,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f6150,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f121,f6143])).

fof(f6143,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f6137,f48])).

fof(f6137,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f6112,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f6112,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2)) ),
    inference(forward_demodulation,[],[f6067,f5330])).

fof(f5330,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k3_xboole_0(X7,X9),X8) = k2_zfmisc_1(k3_xboole_0(X9,X7),X8) ),
    inference(superposition,[],[f4320,f1065])).

fof(f1065,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f61,f78])).

fof(f78,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f74,f38])).

fof(f74,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f40,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f43,f42])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f4320,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k2_zfmisc_1(X9,X8),k2_zfmisc_1(X7,X8)) = k2_zfmisc_1(k3_xboole_0(X7,X9),X8) ),
    inference(superposition,[],[f1065,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6067,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK2)) ),
    inference(superposition,[],[f1349,f168])).

fof(f168,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f152,f38])).

fof(f152,plain,(
    k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f121,f69])).

fof(f69,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK2,sK4)
      | ~ r1_tarski(sK1,sK3) )
    & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK2,sK4)
        | ~ r1_tarski(sK1,sK3) )
      & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
      & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1349,plain,(
    ! [X4,X2,X5,X3] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)),k2_zfmisc_1(k3_xboole_0(X2,X3),X5)) ),
    inference(superposition,[],[f797,f61])).

fof(f797,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,k3_xboole_0(X1,X2)),k2_zfmisc_1(X0,X2)) ),
    inference(resolution,[],[f790,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f121,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X7,X6) ),
    inference(resolution,[],[f58,f90])).

fof(f90,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f76,f39])).

fof(f76,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f64,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f790,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f781,f121])).

fof(f6370,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f6366,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f6366,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f6327,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6327,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) ),
    inference(subsumption_resolution,[],[f6253,f611])).

fof(f611,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 != X1 ) ),
    inference(resolution,[],[f609,f463])).

fof(f463,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0)
      | k1_xboole_0 != X1 ) ),
    inference(forward_demodulation,[],[f460,f38])).

fof(f460,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0)
      | k1_xboole_0 != k4_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f177,f62])).

fof(f177,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5))
      | k1_xboole_0 != k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f609,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,k1_xboole_0)
      | r1_tarski(X19,X20) ) ),
    inference(resolution,[],[f597,f65])).

fof(f65,plain,(
    ! [X0] : sP0(k1_xboole_0,X0,X0) ),
    inference(superposition,[],[f64,f38])).

fof(f597,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ sP0(X3,X4,X5)
      | r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X3) ) ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ sP0(X3,X4,X5)
      | r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X3)
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f179,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X2)
      | ~ sP0(X2,X3,X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6253,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f6066,f6181])).

fof(f6066,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK4)) ),
    inference(superposition,[],[f1349,f144])).

fof(f144,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f141,f38])).

fof(f141,plain,(
    k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f40,f69])).

fof(f36,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (27506)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (27499)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (27489)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27488)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27486)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (27506)Refutation not found, incomplete strategy% (27506)------------------------------
% 0.21/0.51  % (27506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27506)Memory used [KB]: 10746
% 0.21/0.52  % (27506)Time elapsed: 0.050 s
% 0.21/0.52  % (27506)------------------------------
% 0.21/0.52  % (27506)------------------------------
% 0.21/0.52  % (27492)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (27487)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27483)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (27496)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (27491)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (27512)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (27493)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27497)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27485)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27500)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (27513)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (27509)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27511)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27484)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (27494)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27507)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (27510)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (27508)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (27504)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (27503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (27490)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.55  % (27505)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (27502)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (27501)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (27495)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (27501)Refutation not found, incomplete strategy% (27501)------------------------------
% 1.43/0.56  % (27501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (27501)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (27501)Memory used [KB]: 10618
% 1.43/0.56  % (27501)Time elapsed: 0.149 s
% 1.43/0.56  % (27501)------------------------------
% 1.43/0.56  % (27501)------------------------------
% 2.29/0.68  % (27534)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.29/0.70  % (27535)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.59/0.86  % (27488)Time limit reached!
% 3.59/0.86  % (27488)------------------------------
% 3.59/0.86  % (27488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.86  % (27488)Termination reason: Time limit
% 3.59/0.86  % (27488)Termination phase: Saturation
% 3.59/0.86  
% 3.59/0.86  % (27488)Memory used [KB]: 8827
% 3.59/0.86  % (27488)Time elapsed: 0.400 s
% 3.59/0.86  % (27488)------------------------------
% 3.59/0.86  % (27488)------------------------------
% 3.82/0.91  % (27484)Time limit reached!
% 3.82/0.91  % (27484)------------------------------
% 3.82/0.91  % (27484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (27484)Termination reason: Time limit
% 3.82/0.91  % (27484)Termination phase: Saturation
% 3.82/0.91  
% 3.82/0.91  % (27484)Memory used [KB]: 8827
% 3.82/0.91  % (27484)Time elapsed: 0.500 s
% 3.82/0.91  % (27484)------------------------------
% 3.82/0.91  % (27484)------------------------------
% 3.82/0.92  % (27483)Time limit reached!
% 3.82/0.92  % (27483)------------------------------
% 3.82/0.92  % (27483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.92  % (27483)Termination reason: Time limit
% 3.82/0.92  
% 3.82/0.92  % (27483)Memory used [KB]: 2942
% 3.82/0.92  % (27483)Time elapsed: 0.508 s
% 3.82/0.92  % (27483)------------------------------
% 3.82/0.92  % (27483)------------------------------
% 3.82/0.92  % (27495)Time limit reached!
% 3.82/0.92  % (27495)------------------------------
% 3.82/0.92  % (27495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.92  % (27495)Termination reason: Time limit
% 3.82/0.92  % (27495)Termination phase: Saturation
% 3.82/0.92  
% 3.82/0.92  % (27495)Memory used [KB]: 9338
% 3.82/0.92  % (27495)Time elapsed: 0.500 s
% 3.82/0.92  % (27495)------------------------------
% 3.82/0.92  % (27495)------------------------------
% 3.82/0.93  % (27493)Time limit reached!
% 3.82/0.93  % (27493)------------------------------
% 3.82/0.93  % (27493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.94  % (27493)Termination reason: Time limit
% 4.35/0.94  
% 4.35/0.94  % (27493)Memory used [KB]: 15735
% 4.35/0.94  % (27493)Time elapsed: 0.515 s
% 4.35/0.94  % (27493)------------------------------
% 4.35/0.94  % (27493)------------------------------
% 4.35/0.94  % (27535)Refutation not found, incomplete strategy% (27535)------------------------------
% 4.35/0.94  % (27535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.94  % (27535)Termination reason: Refutation not found, incomplete strategy
% 4.35/0.94  
% 4.35/0.94  % (27535)Memory used [KB]: 6524
% 4.35/0.94  % (27535)Time elapsed: 0.357 s
% 4.35/0.94  % (27535)------------------------------
% 4.35/0.94  % (27535)------------------------------
% 4.60/0.98  % (27547)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.60/0.98  % (27490)Refutation found. Thanks to Tanya!
% 4.60/0.98  % SZS status Theorem for theBenchmark
% 4.60/1.00  % SZS output start Proof for theBenchmark
% 4.60/1.00  fof(f6719,plain,(
% 4.60/1.00    $false),
% 4.60/1.00    inference(subsumption_resolution,[],[f6626,f63])).
% 4.60/1.00  fof(f63,plain,(
% 4.60/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.60/1.00    inference(equality_resolution,[],[f45])).
% 4.60/1.00  fof(f45,plain,(
% 4.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.60/1.00    inference(cnf_transformation,[],[f27])).
% 4.60/1.00  fof(f27,plain,(
% 4.60/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.60/1.00    inference(flattening,[],[f26])).
% 4.60/1.00  fof(f26,plain,(
% 4.60/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.60/1.00    inference(nnf_transformation,[],[f7])).
% 4.60/1.00  fof(f7,axiom,(
% 4.60/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 4.60/1.00  fof(f6626,plain,(
% 4.60/1.00    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 4.60/1.00    inference(backward_demodulation,[],[f36,f6624])).
% 4.60/1.00  fof(f6624,plain,(
% 4.60/1.00    k1_xboole_0 = sK1),
% 4.60/1.00    inference(subsumption_resolution,[],[f6601,f62])).
% 4.60/1.00  fof(f62,plain,(
% 4.60/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.60/1.00    inference(equality_resolution,[],[f46])).
% 4.60/1.00  fof(f46,plain,(
% 4.60/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.60/1.00    inference(cnf_transformation,[],[f27])).
% 4.60/1.00  fof(f6601,plain,(
% 4.60/1.00    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 4.60/1.00    inference(superposition,[],[f36,f6374])).
% 4.60/1.00  fof(f6374,plain,(
% 4.60/1.00    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 4.60/1.00    inference(resolution,[],[f6370,f6262])).
% 4.60/1.00  fof(f6262,plain,(
% 4.60/1.00    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 4.60/1.00    inference(superposition,[],[f790,f6181])).
% 4.60/1.01  fof(f6181,plain,(
% 4.60/1.01    sK1 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(forward_demodulation,[],[f6180,f38])).
% 4.60/1.01  fof(f38,plain,(
% 4.60/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.60/1.01    inference(cnf_transformation,[],[f5])).
% 4.60/1.01  fof(f5,axiom,(
% 4.60/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 4.60/1.01  fof(f6180,plain,(
% 4.60/1.01    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(forward_demodulation,[],[f6150,f1001])).
% 4.60/1.01  fof(f1001,plain,(
% 4.60/1.01    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 4.60/1.01    inference(forward_demodulation,[],[f990,f38])).
% 4.60/1.01  fof(f990,plain,(
% 4.60/1.01    ( ! [X2,X1] : (k3_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) )),
% 4.60/1.01    inference(superposition,[],[f40,f821])).
% 4.60/1.01  fof(f821,plain,(
% 4.60/1.01    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 4.60/1.01    inference(resolution,[],[f791,f48])).
% 4.60/1.01  fof(f48,plain,(
% 4.60/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 4.60/1.01    inference(cnf_transformation,[],[f28])).
% 4.60/1.01  fof(f28,plain,(
% 4.60/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.60/1.01    inference(nnf_transformation,[],[f4])).
% 4.60/1.01  fof(f4,axiom,(
% 4.60/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.60/1.01  fof(f791,plain,(
% 4.60/1.01    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X7,X8),X7)) )),
% 4.60/1.01    inference(superposition,[],[f781,f40])).
% 4.60/1.01  fof(f781,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.60/1.01    inference(duplicate_literal_removal,[],[f766])).
% 4.60/1.01  fof(f766,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0) | r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.60/1.01    inference(resolution,[],[f504,f43])).
% 4.60/1.01  fof(f43,plain,(
% 4.60/1.01    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f25])).
% 4.60/1.01  fof(f25,plain,(
% 4.60/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 4.60/1.01  fof(f24,plain,(
% 4.60/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 4.60/1.01    introduced(choice_axiom,[])).
% 4.60/1.01  fof(f23,plain,(
% 4.60/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.60/1.01    inference(rectify,[],[f22])).
% 4.60/1.01  fof(f22,plain,(
% 4.60/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.60/1.01    inference(nnf_transformation,[],[f15])).
% 4.60/1.01  fof(f15,plain,(
% 4.60/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.60/1.01    inference(ennf_transformation,[],[f2])).
% 4.60/1.01  fof(f2,axiom,(
% 4.60/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 4.60/1.01  fof(f504,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK5(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.60/1.01    inference(resolution,[],[f178,f64])).
% 4.60/1.01  fof(f64,plain,(
% 4.60/1.01    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 4.60/1.01    inference(equality_resolution,[],[f57])).
% 4.60/1.01  fof(f57,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.60/1.01    inference(cnf_transformation,[],[f34])).
% 4.60/1.01  fof(f34,plain,(
% 4.60/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 4.60/1.01    inference(nnf_transformation,[],[f19])).
% 4.60/1.01  fof(f19,plain,(
% 4.60/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 4.60/1.01    inference(definition_folding,[],[f3,f18])).
% 4.60/1.01  fof(f18,plain,(
% 4.60/1.01    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.60/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.60/1.01  fof(f3,axiom,(
% 4.60/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.60/1.01  fof(f178,plain,(
% 4.60/1.01    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(resolution,[],[f51,f42])).
% 4.60/1.01  fof(f42,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f25])).
% 4.60/1.01  fof(f51,plain,(
% 4.60/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f33])).
% 4.60/1.01  fof(f33,plain,(
% 4.60/1.01    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 4.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 4.60/1.01  fof(f32,plain,(
% 4.60/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 4.60/1.01    introduced(choice_axiom,[])).
% 4.60/1.01  fof(f31,plain,(
% 4.60/1.01    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 4.60/1.01    inference(rectify,[],[f30])).
% 4.60/1.01  fof(f30,plain,(
% 4.60/1.01    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 4.60/1.01    inference(flattening,[],[f29])).
% 4.60/1.01  fof(f29,plain,(
% 4.60/1.01    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 4.60/1.01    inference(nnf_transformation,[],[f18])).
% 4.60/1.01  fof(f40,plain,(
% 4.60/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.60/1.01    inference(cnf_transformation,[],[f6])).
% 4.60/1.01  fof(f6,axiom,(
% 4.60/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.60/1.01  fof(f6150,plain,(
% 4.60/1.01    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK1) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(superposition,[],[f121,f6143])).
% 4.60/1.01  fof(f6143,plain,(
% 4.60/1.01    k1_xboole_0 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(resolution,[],[f6137,f48])).
% 4.60/1.01  fof(f6137,plain,(
% 4.60/1.01    r1_tarski(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(resolution,[],[f6112,f59])).
% 4.60/1.01  fof(f59,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.60/1.01    inference(cnf_transformation,[],[f17])).
% 4.60/1.01  fof(f17,plain,(
% 4.60/1.01    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 4.60/1.01    inference(ennf_transformation,[],[f8])).
% 4.60/1.01  fof(f8,axiom,(
% 4.60/1.01    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 4.60/1.01  fof(f6112,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2))),
% 4.60/1.01    inference(forward_demodulation,[],[f6067,f5330])).
% 4.60/1.01  fof(f5330,plain,(
% 4.60/1.01    ( ! [X8,X7,X9] : (k2_zfmisc_1(k3_xboole_0(X7,X9),X8) = k2_zfmisc_1(k3_xboole_0(X9,X7),X8)) )),
% 4.60/1.01    inference(superposition,[],[f4320,f1065])).
% 4.60/1.01  fof(f1065,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 4.60/1.01    inference(superposition,[],[f61,f78])).
% 4.60/1.01  fof(f78,plain,(
% 4.60/1.01    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 4.60/1.01    inference(forward_demodulation,[],[f74,f38])).
% 4.60/1.01  fof(f74,plain,(
% 4.60/1.01    ( ! [X1] : (k3_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 4.60/1.01    inference(superposition,[],[f40,f70])).
% 4.60/1.01  fof(f70,plain,(
% 4.60/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.60/1.01    inference(resolution,[],[f48,f67])).
% 4.60/1.01  fof(f67,plain,(
% 4.60/1.01    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 4.60/1.01    inference(duplicate_literal_removal,[],[f66])).
% 4.60/1.01  fof(f66,plain,(
% 4.60/1.01    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 4.60/1.01    inference(resolution,[],[f43,f42])).
% 4.60/1.01  fof(f61,plain,(
% 4.60/1.01    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 4.60/1.01    inference(cnf_transformation,[],[f10])).
% 4.60/1.01  fof(f10,axiom,(
% 4.60/1.01    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 4.60/1.01  fof(f4320,plain,(
% 4.60/1.01    ( ! [X8,X7,X9] : (k3_xboole_0(k2_zfmisc_1(X9,X8),k2_zfmisc_1(X7,X8)) = k2_zfmisc_1(k3_xboole_0(X7,X9),X8)) )),
% 4.60/1.01    inference(superposition,[],[f1065,f39])).
% 4.60/1.01  fof(f39,plain,(
% 4.60/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f1])).
% 4.60/1.01  fof(f1,axiom,(
% 4.60/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.60/1.01  fof(f6067,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK2))),
% 4.60/1.01    inference(superposition,[],[f1349,f168])).
% 4.60/1.01  fof(f168,plain,(
% 4.60/1.01    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2))),
% 4.60/1.01    inference(forward_demodulation,[],[f152,f38])).
% 4.60/1.01  fof(f152,plain,(
% 4.60/1.01    k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k1_xboole_0)),
% 4.60/1.01    inference(superposition,[],[f121,f69])).
% 4.60/1.01  fof(f69,plain,(
% 4.60/1.01    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 4.60/1.01    inference(resolution,[],[f48,f35])).
% 4.60/1.01  fof(f35,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 4.60/1.01    inference(cnf_transformation,[],[f21])).
% 4.60/1.01  fof(f21,plain,(
% 4.60/1.01    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 4.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f20])).
% 4.60/1.01  fof(f20,plain,(
% 4.60/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 4.60/1.01    introduced(choice_axiom,[])).
% 4.60/1.01  fof(f14,plain,(
% 4.60/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 4.60/1.01    inference(flattening,[],[f13])).
% 4.60/1.01  fof(f13,plain,(
% 4.60/1.01    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 4.60/1.01    inference(ennf_transformation,[],[f12])).
% 4.60/1.01  fof(f12,negated_conjecture,(
% 4.60/1.01    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.60/1.01    inference(negated_conjecture,[],[f11])).
% 4.60/1.01  fof(f11,conjecture,(
% 4.60/1.01    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 4.60/1.01  fof(f1349,plain,(
% 4.60/1.01    ( ! [X4,X2,X5,X3] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X5)),k2_zfmisc_1(k3_xboole_0(X2,X3),X5))) )),
% 4.60/1.01    inference(superposition,[],[f797,f61])).
% 4.60/1.01  fof(f797,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,k3_xboole_0(X1,X2)),k2_zfmisc_1(X0,X2))) )),
% 4.60/1.01    inference(resolution,[],[f790,f50])).
% 4.60/1.01  fof(f50,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.60/1.01    inference(cnf_transformation,[],[f16])).
% 4.60/1.01  fof(f16,plain,(
% 4.60/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.60/1.01    inference(ennf_transformation,[],[f9])).
% 4.60/1.01  fof(f9,axiom,(
% 4.60/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 4.60/1.01  fof(f121,plain,(
% 4.60/1.01    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X7,X6)) )),
% 4.60/1.01    inference(resolution,[],[f58,f90])).
% 4.60/1.01  fof(f90,plain,(
% 4.60/1.01    ( ! [X0,X1] : (sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X1,X0))) )),
% 4.60/1.01    inference(superposition,[],[f76,f39])).
% 4.60/1.01  fof(f76,plain,(
% 4.60/1.01    ( ! [X0,X1] : (sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1))) )),
% 4.60/1.01    inference(superposition,[],[f64,f40])).
% 4.60/1.01  fof(f58,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 4.60/1.01    inference(cnf_transformation,[],[f34])).
% 4.60/1.01  fof(f790,plain,(
% 4.60/1.01    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X6,X5),X5)) )),
% 4.60/1.01    inference(superposition,[],[f781,f121])).
% 4.60/1.01  fof(f6370,plain,(
% 4.60/1.01    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1),
% 4.60/1.01    inference(resolution,[],[f6366,f37])).
% 4.60/1.01  fof(f37,plain,(
% 4.60/1.01    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 4.60/1.01    inference(cnf_transformation,[],[f21])).
% 4.60/1.01  fof(f6366,plain,(
% 4.60/1.01    r1_tarski(sK2,sK4) | k1_xboole_0 = sK1),
% 4.60/1.01    inference(resolution,[],[f6327,f60])).
% 4.60/1.01  fof(f60,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.60/1.01    inference(cnf_transformation,[],[f17])).
% 4.60/1.01  fof(f6327,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))),
% 4.60/1.01    inference(subsumption_resolution,[],[f6253,f611])).
% 4.60/1.01  fof(f611,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 != X1) )),
% 4.60/1.01    inference(resolution,[],[f609,f463])).
% 4.60/1.01  fof(f463,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) | k1_xboole_0 != X1) )),
% 4.60/1.01    inference(forward_demodulation,[],[f460,f38])).
% 4.60/1.01  fof(f460,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) | k1_xboole_0 != k4_xboole_0(X1,k1_xboole_0)) )),
% 4.60/1.01    inference(superposition,[],[f177,f62])).
% 4.60/1.01  fof(f177,plain,(
% 4.60/1.01    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) | k1_xboole_0 != k4_xboole_0(X4,X5)) )),
% 4.60/1.01    inference(resolution,[],[f50,f47])).
% 4.60/1.01  fof(f47,plain,(
% 4.60/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.60/1.01    inference(cnf_transformation,[],[f28])).
% 4.60/1.01  fof(f609,plain,(
% 4.60/1.01    ( ! [X19,X20] : (~r1_tarski(X19,k1_xboole_0) | r1_tarski(X19,X20)) )),
% 4.60/1.01    inference(resolution,[],[f597,f65])).
% 4.60/1.01  fof(f65,plain,(
% 4.60/1.01    ( ! [X0] : (sP0(k1_xboole_0,X0,X0)) )),
% 4.60/1.01    inference(superposition,[],[f64,f38])).
% 4.60/1.01  fof(f597,plain,(
% 4.60/1.01    ( ! [X6,X4,X5,X3] : (~sP0(X3,X4,X5) | r1_tarski(X5,X6) | ~r1_tarski(X5,X3)) )),
% 4.60/1.01    inference(duplicate_literal_removal,[],[f596])).
% 4.60/1.01  fof(f596,plain,(
% 4.60/1.01    ( ! [X6,X4,X5,X3] : (~sP0(X3,X4,X5) | r1_tarski(X5,X6) | ~r1_tarski(X5,X3) | r1_tarski(X5,X6)) )),
% 4.60/1.01    inference(resolution,[],[f179,f99])).
% 4.60/1.01  fof(f99,plain,(
% 4.60/1.01    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(resolution,[],[f41,f42])).
% 4.60/1.01  fof(f41,plain,(
% 4.60/1.01    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f25])).
% 4.60/1.01  fof(f179,plain,(
% 4.60/1.01    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1),X2) | ~sP0(X2,X3,X0) | r1_tarski(X0,X1)) )),
% 4.60/1.01    inference(resolution,[],[f52,f42])).
% 4.60/1.01  fof(f52,plain,(
% 4.60/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 4.60/1.01    inference(cnf_transformation,[],[f33])).
% 4.60/1.01  fof(f6253,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) | k1_xboole_0 = sK2),
% 4.60/1.01    inference(superposition,[],[f6066,f6181])).
% 4.60/1.01  fof(f6066,plain,(
% 4.60/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK4))),
% 4.60/1.01    inference(superposition,[],[f1349,f144])).
% 4.60/1.01  fof(f144,plain,(
% 4.60/1.01    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 4.60/1.01    inference(forward_demodulation,[],[f141,f38])).
% 4.60/1.01  fof(f141,plain,(
% 4.60/1.01    k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k1_xboole_0)),
% 4.60/1.01    inference(superposition,[],[f40,f69])).
% 4.60/1.01  fof(f36,plain,(
% 4.60/1.01    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 4.60/1.01    inference(cnf_transformation,[],[f21])).
% 4.60/1.01  % SZS output end Proof for theBenchmark
% 4.60/1.01  % (27490)------------------------------
% 4.60/1.01  % (27490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.01  % (27490)Termination reason: Refutation
% 4.60/1.01  
% 4.60/1.01  % (27490)Memory used [KB]: 10106
% 4.60/1.01  % (27490)Time elapsed: 0.563 s
% 4.60/1.01  % (27490)------------------------------
% 4.60/1.01  % (27490)------------------------------
% 4.60/1.01  % (27479)Success in time 0.636 s
%------------------------------------------------------------------------------
