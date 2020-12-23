%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:39 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 379 expanded)
%              Number of leaves         :   13 ( 101 expanded)
%              Depth                    :   25
%              Number of atoms          :  249 (1406 expanded)
%              Number of equality atoms :   73 ( 253 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2672,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2578,f57])).

fof(f57,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2578,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f33,f2576])).

fof(f2576,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f2563,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2563,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f2561])).

fof(f2561,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f2558,f2309])).

fof(f2309,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f212,f2088])).

fof(f2088,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f2087,f233])).

fof(f233,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f211,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f211,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f209,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f209,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
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

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f2087,plain,
    ( sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f2083,f36])).

fof(f2083,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f2072,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f2072,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2)) ),
    inference(forward_demodulation,[],[f2034,f1091])).

fof(f1091,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k3_xboole_0(X3,X5),X4) = k2_zfmisc_1(k3_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f85,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f85,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X5,X4),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k3_xboole_0(X3,X5),X4) ),
    inference(superposition,[],[f43,f35])).

fof(f2034,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK2)) ),
    inference(superposition,[],[f1241,f63])).

fof(f63,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_tarski(sK2,sK4)
      | ~ r1_tarski(sK1,sK3) )
    & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK2,sK4)
        | ~ r1_tarski(sK1,sK3) )
      & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
      & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1241,plain,(
    ! [X97,X95,X98,X96] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X95,X97),k2_zfmisc_1(X96,X98)),k2_zfmisc_1(k3_xboole_0(X96,X95),X97)) ),
    inference(forward_demodulation,[],[f1176,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f1176,plain,(
    ! [X97,X95,X98,X96] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X95,X96),k3_xboole_0(X97,X98)),k2_zfmisc_1(k3_xboole_0(X96,X95),X97)) ),
    inference(superposition,[],[f401,f1091])).

fof(f401,plain,(
    ! [X30,X28,X29] : r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X29,X30)),k2_zfmisc_1(X28,X29)) ),
    inference(superposition,[],[f209,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f212,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f209,f35])).

fof(f2558,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f2555,f34])).

fof(f34,plain,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2555,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f2298,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2298,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f2039,f2088])).

fof(f2039,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK4)) ),
    inference(superposition,[],[f1241,f79])).

fof(f79,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f77,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    sP0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f59,f63])).

fof(f59,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f58,f35])).

fof(f33,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:12:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.49  % (15996)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (15991)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (16019)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (16007)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (16011)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (16003)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (15998)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (16007)Refutation not found, incomplete strategy% (16007)------------------------------
% 0.20/0.52  % (16007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15995)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (16007)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16007)Memory used [KB]: 10618
% 0.20/0.52  % (16007)Time elapsed: 0.113 s
% 0.20/0.52  % (16007)------------------------------
% 0.20/0.52  % (16007)------------------------------
% 0.20/0.52  % (15994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (15992)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (15993)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (15990)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (16014)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (16018)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (16013)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (16006)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (16016)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (16017)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (16010)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (16012)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (16005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (16012)Refutation not found, incomplete strategy% (16012)------------------------------
% 0.20/0.54  % (16012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16012)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16012)Memory used [KB]: 10746
% 0.20/0.54  % (16012)Time elapsed: 0.134 s
% 0.20/0.54  % (16012)------------------------------
% 0.20/0.54  % (16012)------------------------------
% 0.20/0.54  % (15999)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (16004)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (16002)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (16008)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (16001)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (15997)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (16015)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (16000)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (16009)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.15/0.66  % (16025)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.15/0.70  % (16032)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.15/0.70  % (15997)Refutation found. Thanks to Tanya!
% 2.15/0.70  % SZS status Theorem for theBenchmark
% 2.15/0.70  % SZS output start Proof for theBenchmark
% 2.15/0.70  fof(f2672,plain,(
% 2.15/0.70    $false),
% 2.15/0.70    inference(subsumption_resolution,[],[f2578,f57])).
% 2.15/0.70  fof(f57,plain,(
% 2.15/0.70    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.15/0.70    inference(equality_resolution,[],[f41])).
% 2.15/0.70  fof(f41,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f25])).
% 2.15/0.70  fof(f25,plain,(
% 2.15/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.15/0.70    inference(flattening,[],[f24])).
% 2.15/0.70  fof(f24,plain,(
% 2.15/0.70    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.15/0.70    inference(nnf_transformation,[],[f5])).
% 2.15/0.70  fof(f5,axiom,(
% 2.15/0.70    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.15/0.70  fof(f2578,plain,(
% 2.15/0.70    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 2.15/0.70    inference(backward_demodulation,[],[f33,f2576])).
% 2.15/0.70  fof(f2576,plain,(
% 2.15/0.70    k1_xboole_0 = sK1),
% 2.15/0.70    inference(subsumption_resolution,[],[f2563,f56])).
% 2.15/0.70  fof(f56,plain,(
% 2.15/0.70    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.15/0.70    inference(equality_resolution,[],[f42])).
% 2.15/0.70  fof(f42,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.15/0.70    inference(cnf_transformation,[],[f25])).
% 2.15/0.70  fof(f2563,plain,(
% 2.15/0.70    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 2.15/0.70    inference(superposition,[],[f33,f2561])).
% 2.15/0.70  fof(f2561,plain,(
% 2.15/0.70    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.15/0.70    inference(subsumption_resolution,[],[f2558,f2309])).
% 2.15/0.70  fof(f2309,plain,(
% 2.15/0.70    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 2.15/0.70    inference(superposition,[],[f212,f2088])).
% 2.15/0.70  fof(f2088,plain,(
% 2.15/0.70    sK1 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = sK2),
% 2.15/0.70    inference(superposition,[],[f2087,f233])).
% 2.15/0.70  fof(f233,plain,(
% 2.15/0.70    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.15/0.70    inference(superposition,[],[f211,f35])).
% 2.15/0.70  fof(f35,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f1])).
% 2.15/0.70  fof(f1,axiom,(
% 2.15/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.15/0.70  fof(f211,plain,(
% 2.15/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X3)) )),
% 2.15/0.70    inference(resolution,[],[f209,f36])).
% 2.15/0.70  fof(f36,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f13])).
% 2.15/0.70  fof(f13,plain,(
% 2.15/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f4])).
% 2.15/0.70  fof(f4,axiom,(
% 2.15/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.15/0.70  fof(f209,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.15/0.70    inference(duplicate_literal_removal,[],[f199])).
% 2.15/0.70  fof(f199,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.15/0.70    inference(resolution,[],[f129,f39])).
% 2.15/0.70  fof(f39,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f23])).
% 2.15/0.70  fof(f23,plain,(
% 2.15/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 2.15/0.70  fof(f22,plain,(
% 2.15/0.70    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f21,plain,(
% 2.15/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.70    inference(rectify,[],[f20])).
% 2.15/0.70  fof(f20,plain,(
% 2.15/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.15/0.70    inference(nnf_transformation,[],[f14])).
% 2.15/0.70  fof(f14,plain,(
% 2.15/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.15/0.70    inference(ennf_transformation,[],[f2])).
% 2.15/0.70  fof(f2,axiom,(
% 2.15/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.15/0.70  fof(f129,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.15/0.70    inference(resolution,[],[f73,f58])).
% 2.15/0.70  fof(f58,plain,(
% 2.15/0.70    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 2.15/0.70    inference(equality_resolution,[],[f51])).
% 2.15/0.70  fof(f51,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.15/0.70    inference(cnf_transformation,[],[f31])).
% 2.15/0.70  fof(f31,plain,(
% 2.15/0.70    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.15/0.70    inference(nnf_transformation,[],[f17])).
% 2.15/0.70  fof(f17,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.15/0.70    inference(definition_folding,[],[f3,f16])).
% 2.15/0.70  fof(f16,plain,(
% 2.15/0.70    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.15/0.70  fof(f3,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.15/0.70  fof(f73,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.15/0.70    inference(resolution,[],[f45,f38])).
% 2.15/0.70  fof(f38,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f23])).
% 2.15/0.70  fof(f45,plain,(
% 2.15/0.70    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f30])).
% 2.15/0.70  fof(f30,plain,(
% 2.15/0.70    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 2.15/0.70  fof(f29,plain,(
% 2.15/0.70    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f28,plain,(
% 2.15/0.70    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.15/0.70    inference(rectify,[],[f27])).
% 2.15/0.70  fof(f27,plain,(
% 2.15/0.70    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.15/0.70    inference(flattening,[],[f26])).
% 2.15/0.70  fof(f26,plain,(
% 2.15/0.70    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.15/0.70    inference(nnf_transformation,[],[f16])).
% 2.15/0.70  fof(f2087,plain,(
% 2.15/0.70    sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK2),
% 2.15/0.70    inference(resolution,[],[f2083,f36])).
% 2.15/0.70  fof(f2083,plain,(
% 2.15/0.70    r1_tarski(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK2),
% 2.15/0.70    inference(resolution,[],[f2072,f53])).
% 2.15/0.70  fof(f53,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f15])).
% 2.15/0.70  fof(f15,plain,(
% 2.15/0.70    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 2.15/0.70    inference(ennf_transformation,[],[f6])).
% 2.15/0.70  fof(f6,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 2.15/0.70  fof(f2072,plain,(
% 2.15/0.70    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2))),
% 2.15/0.70    inference(forward_demodulation,[],[f2034,f1091])).
% 2.15/0.70  fof(f1091,plain,(
% 2.15/0.70    ( ! [X4,X5,X3] : (k2_zfmisc_1(k3_xboole_0(X3,X5),X4) = k2_zfmisc_1(k3_xboole_0(X5,X3),X4)) )),
% 2.15/0.70    inference(superposition,[],[f85,f43])).
% 2.15/0.70  fof(f43,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f7])).
% 2.15/0.70  fof(f7,axiom,(
% 2.15/0.70    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 2.15/0.70  fof(f85,plain,(
% 2.15/0.70    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X5,X4),k2_zfmisc_1(X3,X4)) = k2_zfmisc_1(k3_xboole_0(X3,X5),X4)) )),
% 2.15/0.70    inference(superposition,[],[f43,f35])).
% 2.15/0.70  fof(f2034,plain,(
% 2.15/0.70    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK2))),
% 2.15/0.70    inference(superposition,[],[f1241,f63])).
% 2.15/0.70  fof(f63,plain,(
% 2.15/0.70    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.15/0.70    inference(resolution,[],[f36,f32])).
% 2.15/0.70  fof(f32,plain,(
% 2.15/0.70    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.15/0.70    inference(cnf_transformation,[],[f19])).
% 2.15/0.70  fof(f19,plain,(
% 2.15/0.70    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).
% 2.15/0.70  fof(f18,plain,(
% 2.15/0.70    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f12,plain,(
% 2.15/0.70    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.15/0.70    inference(flattening,[],[f11])).
% 2.15/0.70  fof(f11,plain,(
% 2.15/0.70    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.15/0.70    inference(ennf_transformation,[],[f10])).
% 2.15/0.70  fof(f10,negated_conjecture,(
% 2.15/0.70    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 2.15/0.70    inference(negated_conjecture,[],[f9])).
% 2.15/0.70  fof(f9,conjecture,(
% 2.15/0.70    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.15/0.70  fof(f1241,plain,(
% 2.15/0.70    ( ! [X97,X95,X98,X96] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X95,X97),k2_zfmisc_1(X96,X98)),k2_zfmisc_1(k3_xboole_0(X96,X95),X97))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f1176,f55])).
% 2.15/0.70  fof(f55,plain,(
% 2.15/0.70    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f8])).
% 2.15/0.70  fof(f8,axiom,(
% 2.15/0.70    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.15/0.70  fof(f1176,plain,(
% 2.15/0.70    ( ! [X97,X95,X98,X96] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X95,X96),k3_xboole_0(X97,X98)),k2_zfmisc_1(k3_xboole_0(X96,X95),X97))) )),
% 2.15/0.70    inference(superposition,[],[f401,f1091])).
% 2.15/0.70  fof(f401,plain,(
% 2.15/0.70    ( ! [X30,X28,X29] : (r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X29,X30)),k2_zfmisc_1(X28,X29))) )),
% 2.15/0.70    inference(superposition,[],[f209,f44])).
% 2.15/0.70  fof(f44,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f7])).
% 2.15/0.70  fof(f212,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.15/0.70    inference(superposition,[],[f209,f35])).
% 2.15/0.70  fof(f2558,plain,(
% 2.15/0.70    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK3)),
% 2.15/0.70    inference(resolution,[],[f2555,f34])).
% 2.15/0.70  fof(f34,plain,(
% 2.15/0.70    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 2.15/0.70    inference(cnf_transformation,[],[f19])).
% 2.15/0.70  fof(f2555,plain,(
% 2.15/0.70    r1_tarski(sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.15/0.70    inference(resolution,[],[f2298,f54])).
% 2.15/0.70  fof(f54,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f15])).
% 2.15/0.70  fof(f2298,plain,(
% 2.15/0.70    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) | k1_xboole_0 = sK2),
% 2.15/0.70    inference(superposition,[],[f2039,f2088])).
% 2.15/0.70  fof(f2039,plain,(
% 2.15/0.70    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK4))),
% 2.15/0.70    inference(superposition,[],[f1241,f79])).
% 2.15/0.70  fof(f79,plain,(
% 2.15/0.70    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2))),
% 2.15/0.70    inference(resolution,[],[f77,f52])).
% 2.15/0.70  fof(f52,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.15/0.70    inference(cnf_transformation,[],[f31])).
% 2.15/0.70  fof(f77,plain,(
% 2.15/0.70    sP0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2))),
% 2.15/0.70    inference(superposition,[],[f59,f63])).
% 2.15/0.70  fof(f59,plain,(
% 2.15/0.70    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X1,X0))) )),
% 2.15/0.70    inference(superposition,[],[f58,f35])).
% 2.15/0.70  fof(f33,plain,(
% 2.15/0.70    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 2.15/0.70    inference(cnf_transformation,[],[f19])).
% 2.15/0.70  % SZS output end Proof for theBenchmark
% 2.15/0.70  % (15997)------------------------------
% 2.15/0.70  % (15997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (15997)Termination reason: Refutation
% 2.15/0.70  
% 2.15/0.70  % (15997)Memory used [KB]: 8059
% 2.15/0.70  % (15997)Time elapsed: 0.263 s
% 2.15/0.70  % (15997)------------------------------
% 2.15/0.70  % (15997)------------------------------
% 2.78/0.72  % (15989)Success in time 0.367 s
%------------------------------------------------------------------------------
