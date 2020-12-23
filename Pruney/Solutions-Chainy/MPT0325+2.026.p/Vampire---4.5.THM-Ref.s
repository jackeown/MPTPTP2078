%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 432 expanded)
%              Number of leaves         :   15 ( 108 expanded)
%              Depth                    :   26
%              Number of atoms          :  315 (1894 expanded)
%              Number of equality atoms :   83 ( 209 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1654,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1610,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1610,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f39,f1608])).

fof(f1608,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1585,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1585,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f39,f1578])).

fof(f1578,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1572,f1553])).

fof(f1553,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1533,f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK2,sK4)
      | ~ r1_tarski(sK1,sK3) )
    & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f21])).

fof(f21,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1533,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f460,f1506])).

fof(f1506,plain,
    ( sK2 = k3_xboole_0(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1494,f244])).

fof(f244,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k3_xboole_0(X6,X7))
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f241,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f241,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f219,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f126,f71])).

fof(f71,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f1494,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK4))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1465,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1465,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f805,f73])).

fof(f73,plain,(
    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f805,plain,(
    ! [X14,X12,X15,X13] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)),k2_zfmisc_1(X12,k3_xboole_0(X14,X15))) ),
    inference(superposition,[],[f243,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f243,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5)) ),
    inference(resolution,[],[f241,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f460,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f223,f48])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f127,f71])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X3,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1572,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1552,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1552,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f1514,f388])).

fof(f388,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4))
      | k1_xboole_0 != X3 ) ),
    inference(resolution,[],[f385,f54])).

fof(f385,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f276,f48])).

fof(f276,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK5(X13,X14),X15)
      | k1_xboole_0 != X13
      | r1_tarski(X13,X14) ) ),
    inference(subsumption_resolution,[],[f231,f269])).

fof(f269,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f261,f48])).

fof(f261,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f260,f127])).

fof(f260,plain,(
    ! [X4] : sP0(X4,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f71,f253])).

fof(f253,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f245,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f245,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8) ),
    inference(resolution,[],[f241,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f231,plain,(
    ! [X14,X15,X13] :
      ( r1_tarski(X13,X14)
      | k1_xboole_0 != X13
      | r2_hidden(sK5(X13,X14),X15)
      | ~ r1_tarski(k1_xboole_0,X15) ) ),
    inference(resolution,[],[f225,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f225,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(X5,X6),k1_xboole_0)
      | r1_tarski(X5,X6)
      | k1_xboole_0 != X5 ) ),
    inference(resolution,[],[f127,f84])).

fof(f84,plain,(
    ! [X0] :
      ( sP0(k1_xboole_0,X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f71,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k1_xboole_0) = X0
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f52,f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1514,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1413,f1506])).

fof(f1413,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f803,f73])).

fof(f803,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X5,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f462,f66])).

fof(f462,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5)) ),
    inference(resolution,[],[f460,f54])).

fof(f39,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (16325)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (16342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (16346)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (16322)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (16320)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (16342)Refutation not found, incomplete strategy% (16342)------------------------------
% 0.22/0.53  % (16342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16342)Memory used [KB]: 10746
% 0.22/0.53  % (16342)Time elapsed: 0.121 s
% 0.22/0.53  % (16342)------------------------------
% 0.22/0.53  % (16342)------------------------------
% 0.22/0.54  % (16349)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (16323)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (16343)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (16339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (16328)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (16330)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (16321)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (16345)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (16327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (16337)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (16329)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (16326)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (16331)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (16332)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (16344)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (16341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (16335)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (16338)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (16324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (16334)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (16340)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (16333)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.58  % (16348)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (16336)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (16337)Refutation not found, incomplete strategy% (16337)------------------------------
% 0.22/0.58  % (16337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (16337)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (16337)Memory used [KB]: 10618
% 0.22/0.58  % (16337)Time elapsed: 0.156 s
% 0.22/0.58  % (16337)------------------------------
% 0.22/0.58  % (16337)------------------------------
% 0.22/0.59  % (16347)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.99/0.67  % (16371)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.69  % (16327)Refutation found. Thanks to Tanya!
% 1.99/0.69  % SZS status Theorem for theBenchmark
% 1.99/0.69  % SZS output start Proof for theBenchmark
% 1.99/0.69  fof(f1654,plain,(
% 1.99/0.69    $false),
% 1.99/0.69    inference(subsumption_resolution,[],[f1610,f70])).
% 1.99/0.69  fof(f70,plain,(
% 1.99/0.69    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.99/0.69    inference(equality_resolution,[],[f50])).
% 1.99/0.69  fof(f50,plain,(
% 1.99/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f30])).
% 1.99/0.69  fof(f30,plain,(
% 1.99/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.99/0.69    inference(flattening,[],[f29])).
% 1.99/0.69  fof(f29,plain,(
% 1.99/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.99/0.69    inference(nnf_transformation,[],[f7])).
% 1.99/0.69  fof(f7,axiom,(
% 1.99/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.99/0.69  fof(f1610,plain,(
% 1.99/0.69    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 1.99/0.69    inference(backward_demodulation,[],[f39,f1608])).
% 1.99/0.69  fof(f1608,plain,(
% 1.99/0.69    k1_xboole_0 = sK1),
% 1.99/0.69    inference(subsumption_resolution,[],[f1585,f69])).
% 1.99/0.69  fof(f69,plain,(
% 1.99/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.99/0.69    inference(equality_resolution,[],[f51])).
% 1.99/0.69  fof(f51,plain,(
% 1.99/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.99/0.69    inference(cnf_transformation,[],[f30])).
% 1.99/0.69  fof(f1585,plain,(
% 1.99/0.69    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(superposition,[],[f39,f1578])).
% 1.99/0.69  fof(f1578,plain,(
% 1.99/0.69    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.99/0.69    inference(resolution,[],[f1572,f1553])).
% 1.99/0.69  fof(f1553,plain,(
% 1.99/0.69    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(resolution,[],[f1533,f40])).
% 1.99/0.69  fof(f40,plain,(
% 1.99/0.69    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 1.99/0.69    inference(cnf_transformation,[],[f22])).
% 1.99/0.69  fof(f22,plain,(
% 1.99/0.69    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 1.99/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f21])).
% 1.99/0.69  fof(f21,plain,(
% 1.99/0.69    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 1.99/0.69    introduced(choice_axiom,[])).
% 1.99/0.69  fof(f14,plain,(
% 1.99/0.69    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.99/0.69    inference(flattening,[],[f13])).
% 1.99/0.69  fof(f13,plain,(
% 1.99/0.69    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.99/0.69    inference(ennf_transformation,[],[f12])).
% 1.99/0.69  fof(f12,negated_conjecture,(
% 1.99/0.69    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.99/0.69    inference(negated_conjecture,[],[f11])).
% 1.99/0.69  fof(f11,conjecture,(
% 1.99/0.69    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.99/0.69  fof(f1533,plain,(
% 1.99/0.69    r1_tarski(sK2,sK4) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(superposition,[],[f460,f1506])).
% 1.99/0.69  fof(f1506,plain,(
% 1.99/0.69    sK2 = k3_xboole_0(sK2,sK4) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(resolution,[],[f1494,f244])).
% 1.99/0.69  fof(f244,plain,(
% 1.99/0.69    ( ! [X6,X7] : (~r1_tarski(X6,k3_xboole_0(X6,X7)) | k3_xboole_0(X6,X7) = X6) )),
% 1.99/0.69    inference(resolution,[],[f241,f45])).
% 1.99/0.69  fof(f45,plain,(
% 1.99/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.99/0.69    inference(cnf_transformation,[],[f24])).
% 1.99/0.69  fof(f24,plain,(
% 1.99/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.69    inference(flattening,[],[f23])).
% 1.99/0.69  fof(f23,plain,(
% 1.99/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.69    inference(nnf_transformation,[],[f3])).
% 1.99/0.69  fof(f3,axiom,(
% 1.99/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.99/0.69  fof(f241,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.99/0.69    inference(duplicate_literal_removal,[],[f233])).
% 1.99/0.69  fof(f233,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.99/0.69    inference(resolution,[],[f219,f48])).
% 1.99/0.69  fof(f48,plain,(
% 1.99/0.69    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f28])).
% 1.99/0.69  fof(f28,plain,(
% 1.99/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.99/0.69  fof(f27,plain,(
% 1.99/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.99/0.69    introduced(choice_axiom,[])).
% 1.99/0.69  fof(f26,plain,(
% 1.99/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.69    inference(rectify,[],[f25])).
% 1.99/0.69  fof(f25,plain,(
% 1.99/0.69    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.69    inference(nnf_transformation,[],[f16])).
% 1.99/0.69  fof(f16,plain,(
% 1.99/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.99/0.69    inference(ennf_transformation,[],[f1])).
% 1.99/0.69  fof(f1,axiom,(
% 1.99/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.99/0.69  fof(f219,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.99/0.69    inference(resolution,[],[f126,f71])).
% 1.99/0.69  fof(f71,plain,(
% 1.99/0.69    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.99/0.69    inference(equality_resolution,[],[f62])).
% 1.99/0.69  fof(f62,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.99/0.69    inference(cnf_transformation,[],[f37])).
% 1.99/0.69  fof(f37,plain,(
% 1.99/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.99/0.69    inference(nnf_transformation,[],[f20])).
% 1.99/0.69  fof(f20,plain,(
% 1.99/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.99/0.69    inference(definition_folding,[],[f2,f19])).
% 1.99/0.69  fof(f19,plain,(
% 1.99/0.69    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.99/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.99/0.69  fof(f2,axiom,(
% 1.99/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.99/0.69  fof(f126,plain,(
% 1.99/0.69    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(resolution,[],[f56,f47])).
% 1.99/0.69  fof(f47,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f28])).
% 1.99/0.69  fof(f56,plain,(
% 1.99/0.69    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f36])).
% 1.99/0.69  fof(f36,plain,(
% 1.99/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.99/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 1.99/0.69  fof(f35,plain,(
% 1.99/0.69    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.99/0.69    introduced(choice_axiom,[])).
% 1.99/0.69  fof(f34,plain,(
% 1.99/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.99/0.69    inference(rectify,[],[f33])).
% 1.99/0.69  fof(f33,plain,(
% 1.99/0.69    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.99/0.69    inference(flattening,[],[f32])).
% 1.99/0.69  fof(f32,plain,(
% 1.99/0.69    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.99/0.69    inference(nnf_transformation,[],[f19])).
% 1.99/0.69  fof(f1494,plain,(
% 1.99/0.69    r1_tarski(sK2,k3_xboole_0(sK2,sK4)) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(resolution,[],[f1465,f65])).
% 1.99/0.69  fof(f65,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f18])).
% 1.99/0.69  fof(f18,plain,(
% 1.99/0.69    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.99/0.69    inference(ennf_transformation,[],[f8])).
% 1.99/0.69  fof(f8,axiom,(
% 1.99/0.69    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.99/0.69  fof(f1465,plain,(
% 1.99/0.69    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)))),
% 1.99/0.69    inference(superposition,[],[f805,f73])).
% 1.99/0.69  fof(f73,plain,(
% 1.99/0.69    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 1.99/0.69    inference(resolution,[],[f42,f38])).
% 1.99/0.69  fof(f38,plain,(
% 1.99/0.69    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 1.99/0.69    inference(cnf_transformation,[],[f22])).
% 1.99/0.69  fof(f42,plain,(
% 1.99/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f15])).
% 1.99/0.69  fof(f15,plain,(
% 1.99/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.99/0.69    inference(ennf_transformation,[],[f5])).
% 1.99/0.69  fof(f5,axiom,(
% 1.99/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.99/0.69  fof(f805,plain,(
% 1.99/0.69    ( ! [X14,X12,X15,X13] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)),k2_zfmisc_1(X12,k3_xboole_0(X14,X15)))) )),
% 1.99/0.69    inference(superposition,[],[f243,f66])).
% 1.99/0.69  fof(f66,plain,(
% 1.99/0.69    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.99/0.69    inference(cnf_transformation,[],[f10])).
% 1.99/0.69  fof(f10,axiom,(
% 1.99/0.69    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.99/0.69  fof(f243,plain,(
% 1.99/0.69    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5))) )),
% 1.99/0.69    inference(resolution,[],[f241,f54])).
% 1.99/0.69  fof(f54,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.99/0.69    inference(cnf_transformation,[],[f17])).
% 1.99/0.69  fof(f17,plain,(
% 1.99/0.69    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.99/0.69    inference(ennf_transformation,[],[f9])).
% 1.99/0.69  fof(f9,axiom,(
% 1.99/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.99/0.69  fof(f460,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.99/0.69    inference(duplicate_literal_removal,[],[f450])).
% 1.99/0.69  fof(f450,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.99/0.69    inference(resolution,[],[f223,f48])).
% 1.99/0.69  fof(f223,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.99/0.69    inference(resolution,[],[f127,f71])).
% 1.99/0.69  fof(f127,plain,(
% 1.99/0.69    ( ! [X2,X0,X3,X1] : (~sP0(X2,X3,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(resolution,[],[f57,f47])).
% 1.99/0.69  fof(f57,plain,(
% 1.99/0.69    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f36])).
% 1.99/0.69  fof(f1572,plain,(
% 1.99/0.69    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 1.99/0.69    inference(resolution,[],[f1552,f64])).
% 1.99/0.69  fof(f64,plain,(
% 1.99/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f18])).
% 1.99/0.69  fof(f1552,plain,(
% 1.99/0.69    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))),
% 1.99/0.69    inference(subsumption_resolution,[],[f1514,f388])).
% 1.99/0.69  fof(f388,plain,(
% 1.99/0.69    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) | k1_xboole_0 != X3) )),
% 1.99/0.69    inference(resolution,[],[f385,f54])).
% 1.99/0.69  fof(f385,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != X0) )),
% 1.99/0.69    inference(duplicate_literal_removal,[],[f380])).
% 1.99/0.69  fof(f380,plain,(
% 1.99/0.69    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,X1) | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(resolution,[],[f276,f48])).
% 1.99/0.69  fof(f276,plain,(
% 1.99/0.69    ( ! [X14,X15,X13] : (r2_hidden(sK5(X13,X14),X15) | k1_xboole_0 != X13 | r1_tarski(X13,X14)) )),
% 1.99/0.69    inference(subsumption_resolution,[],[f231,f269])).
% 1.99/0.69  fof(f269,plain,(
% 1.99/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.99/0.69    inference(duplicate_literal_removal,[],[f264])).
% 1.99/0.69  fof(f264,plain,(
% 1.99/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.99/0.69    inference(resolution,[],[f261,f48])).
% 1.99/0.69  fof(f261,plain,(
% 1.99/0.69    ( ! [X0,X1] : (r2_hidden(sK5(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,X0)) )),
% 1.99/0.69    inference(resolution,[],[f260,f127])).
% 1.99/0.69  fof(f260,plain,(
% 1.99/0.69    ( ! [X4] : (sP0(X4,k1_xboole_0,k1_xboole_0)) )),
% 1.99/0.69    inference(superposition,[],[f71,f253])).
% 1.99/0.69  fof(f253,plain,(
% 1.99/0.69    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 1.99/0.69    inference(superposition,[],[f245,f41])).
% 1.99/0.69  fof(f41,plain,(
% 1.99/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f6])).
% 1.99/0.69  fof(f6,axiom,(
% 1.99/0.69    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.99/0.69  fof(f245,plain,(
% 1.99/0.69    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X8,X9),X8)) )),
% 1.99/0.69    inference(resolution,[],[f241,f53])).
% 1.99/0.69  fof(f53,plain,(
% 1.99/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.99/0.69    inference(cnf_transformation,[],[f31])).
% 1.99/0.69  fof(f31,plain,(
% 1.99/0.69    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.99/0.69    inference(nnf_transformation,[],[f4])).
% 1.99/0.69  fof(f4,axiom,(
% 1.99/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.99/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.99/0.69  fof(f231,plain,(
% 1.99/0.69    ( ! [X14,X15,X13] : (r1_tarski(X13,X14) | k1_xboole_0 != X13 | r2_hidden(sK5(X13,X14),X15) | ~r1_tarski(k1_xboole_0,X15)) )),
% 1.99/0.69    inference(resolution,[],[f225,f46])).
% 1.99/0.69  fof(f46,plain,(
% 1.99/0.69    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f28])).
% 1.99/0.69  fof(f225,plain,(
% 1.99/0.69    ( ! [X6,X5] : (r2_hidden(sK5(X5,X6),k1_xboole_0) | r1_tarski(X5,X6) | k1_xboole_0 != X5) )),
% 1.99/0.69    inference(resolution,[],[f127,f84])).
% 1.99/0.69  fof(f84,plain,(
% 1.99/0.69    ( ! [X0] : (sP0(k1_xboole_0,X0,X0) | k1_xboole_0 != X0) )),
% 1.99/0.69    inference(superposition,[],[f71,f78])).
% 1.99/0.69  fof(f78,plain,(
% 1.99/0.69    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = X0 | k1_xboole_0 != X0) )),
% 1.99/0.69    inference(resolution,[],[f77,f42])).
% 1.99/0.69  fof(f77,plain,(
% 1.99/0.69    ( ! [X0] : (r1_tarski(X0,k1_xboole_0) | k1_xboole_0 != X0) )),
% 1.99/0.69    inference(superposition,[],[f52,f41])).
% 1.99/0.69  fof(f52,plain,(
% 1.99/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.99/0.69    inference(cnf_transformation,[],[f31])).
% 1.99/0.69  fof(f1514,plain,(
% 1.99/0.69    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 1.99/0.69    inference(superposition,[],[f1413,f1506])).
% 1.99/0.69  fof(f1413,plain,(
% 1.99/0.69    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))),
% 1.99/0.69    inference(superposition,[],[f803,f73])).
% 1.99/0.69  fof(f803,plain,(
% 1.99/0.69    ( ! [X6,X4,X7,X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X5,k3_xboole_0(X6,X7)))) )),
% 1.99/0.69    inference(superposition,[],[f462,f66])).
% 1.99/0.69  fof(f462,plain,(
% 1.99/0.69    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5))) )),
% 1.99/0.69    inference(resolution,[],[f460,f54])).
% 1.99/0.69  fof(f39,plain,(
% 1.99/0.69    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 1.99/0.69    inference(cnf_transformation,[],[f22])).
% 1.99/0.69  % SZS output end Proof for theBenchmark
% 1.99/0.69  % (16327)------------------------------
% 1.99/0.69  % (16327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.69  % (16327)Termination reason: Refutation
% 1.99/0.69  
% 1.99/0.69  % (16327)Memory used [KB]: 7547
% 1.99/0.69  % (16327)Time elapsed: 0.246 s
% 1.99/0.69  % (16327)------------------------------
% 1.99/0.69  % (16327)------------------------------
% 1.99/0.70  % (16319)Success in time 0.323 s
%------------------------------------------------------------------------------
