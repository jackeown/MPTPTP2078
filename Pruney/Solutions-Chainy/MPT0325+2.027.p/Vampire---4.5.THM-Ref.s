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
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 449 expanded)
%              Number of leaves         :   15 ( 110 expanded)
%              Depth                    :   24
%              Number of atoms          :  322 (1863 expanded)
%              Number of equality atoms :   88 ( 259 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1802,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1758,f70])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1758,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f39,f1756])).

fof(f1756,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1733,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1733,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f39,f1726])).

fof(f1726,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1720,f1701])).

fof(f1701,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1680,f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f1680,plain,
    ( r1_tarski(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f525,f1651])).

fof(f1651,plain,
    ( sK2 = k3_xboole_0(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1639,f382])).

fof(f382,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k3_xboole_0(X6,X7))
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f379,f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f379,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f258,f48])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f139,f71])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f139,plain,(
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

fof(f1639,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,sK4))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1610,f65])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1610,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f1094,f73])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1094,plain,(
    ! [X14,X12,X15,X13] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)),k2_zfmisc_1(X12,k3_xboole_0(X14,X15))) ),
    inference(superposition,[],[f381,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f381,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5)) ),
    inference(resolution,[],[f379,f54])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f525,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f514])).

fof(f514,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f305,f48])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f140,f71])).

fof(f140,plain,(
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

fof(f1720,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1699,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1699,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f1659,f328])).

fof(f328,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4))
      | k1_xboole_0 != X3 ) ),
    inference(resolution,[],[f321,f54])).

fof(f321,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f316,f48])).

fof(f316,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK5(X9,X10),X11)
      | k1_xboole_0 != X9
      | r1_tarski(X9,X10) ) ),
    inference(subsumption_resolution,[],[f314,f267])).

fof(f267,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f260,f48])).

fof(f260,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(k1_xboole_0,X5),X6)
      | r1_tarski(k1_xboole_0,X5) ) ),
    inference(resolution,[],[f139,f88])).

fof(f88,plain,(
    ! [X0] : sP0(k1_xboole_0,X0,k1_xboole_0) ),
    inference(superposition,[],[f71,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f85,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f85,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f41,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f81,f72])).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f42,f67])).

fof(f81,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f41,f77])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f314,plain,(
    ! [X10,X11,X9] :
      ( r1_tarski(X9,X10)
      | k1_xboole_0 != X9
      | r2_hidden(sK5(X9,X10),X11)
      | ~ r1_tarski(k1_xboole_0,X11) ) ),
    inference(resolution,[],[f309,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f309,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK5(X8,X9),k1_xboole_0)
      | r1_tarski(X8,X9)
      | k1_xboole_0 != X8 ) ),
    inference(resolution,[],[f140,f94])).

fof(f94,plain,(
    ! [X1] :
      ( sP0(k1_xboole_0,X1,X1)
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f71,f90])).

fof(f90,plain,(
    ! [X1] :
      ( k3_xboole_0(X1,k1_xboole_0) = X1
      | k1_xboole_0 != X1 ) ),
    inference(resolution,[],[f86,f42])).

fof(f86,plain,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f52,f84])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1659,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1549,f1651])).

fof(f1549,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f1092,f73])).

fof(f1092,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X5,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f527,f66])).

fof(f527,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5)) ),
    inference(resolution,[],[f525,f54])).

fof(f39,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5455)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (5470)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (5466)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (5463)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (5470)Refutation not found, incomplete strategy% (5470)------------------------------
% 0.21/0.52  % (5470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5454)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (5470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5470)Memory used [KB]: 10618
% 0.21/0.52  % (5470)Time elapsed: 0.119 s
% 0.21/0.52  % (5470)------------------------------
% 0.21/0.52  % (5470)------------------------------
% 0.21/0.53  % (5468)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (5453)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (5458)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (5456)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5482)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5459)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.54  % (5478)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.54  % (5472)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.54  % (5479)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.54  % (5460)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.55  % (5474)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (5476)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (5480)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (5481)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (5471)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (5477)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (5461)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (5457)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.55  % (5469)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.55  % (5465)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (5464)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (5473)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.56  % (5462)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.57  % (5467)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.58  % (5475)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.58  % (5475)Refutation not found, incomplete strategy% (5475)------------------------------
% 1.53/0.58  % (5475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (5475)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (5475)Memory used [KB]: 10746
% 1.53/0.59  % (5475)Time elapsed: 0.148 s
% 1.53/0.59  % (5475)------------------------------
% 1.53/0.59  % (5475)------------------------------
% 2.34/0.70  % (5486)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.34/0.73  % (5460)Refutation found. Thanks to Tanya!
% 2.34/0.73  % SZS status Theorem for theBenchmark
% 2.34/0.73  % SZS output start Proof for theBenchmark
% 2.34/0.73  fof(f1802,plain,(
% 2.34/0.73    $false),
% 2.34/0.73    inference(subsumption_resolution,[],[f1758,f70])).
% 2.34/0.73  fof(f70,plain,(
% 2.34/0.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.34/0.73    inference(equality_resolution,[],[f50])).
% 2.34/0.73  fof(f50,plain,(
% 2.34/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.34/0.73    inference(cnf_transformation,[],[f30])).
% 2.34/0.73  fof(f30,plain,(
% 2.34/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.34/0.73    inference(flattening,[],[f29])).
% 2.34/0.73  fof(f29,plain,(
% 2.34/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.34/0.73    inference(nnf_transformation,[],[f7])).
% 2.34/0.73  fof(f7,axiom,(
% 2.34/0.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.34/0.73  fof(f1758,plain,(
% 2.34/0.73    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 2.34/0.73    inference(backward_demodulation,[],[f39,f1756])).
% 2.34/0.73  fof(f1756,plain,(
% 2.34/0.73    k1_xboole_0 = sK1),
% 2.34/0.73    inference(subsumption_resolution,[],[f1733,f69])).
% 2.34/0.73  fof(f69,plain,(
% 2.34/0.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.34/0.73    inference(equality_resolution,[],[f51])).
% 2.34/0.73  fof(f51,plain,(
% 2.34/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.34/0.73    inference(cnf_transformation,[],[f30])).
% 2.34/0.73  fof(f1733,plain,(
% 2.34/0.73    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(superposition,[],[f39,f1726])).
% 2.34/0.73  fof(f1726,plain,(
% 2.34/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.34/0.73    inference(resolution,[],[f1720,f1701])).
% 2.34/0.73  fof(f1701,plain,(
% 2.34/0.73    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(resolution,[],[f1680,f40])).
% 2.34/0.73  fof(f40,plain,(
% 2.34/0.73    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 2.34/0.73    inference(cnf_transformation,[],[f22])).
% 2.34/0.73  fof(f22,plain,(
% 2.34/0.73    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.34/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f21])).
% 2.34/0.73  fof(f21,plain,(
% 2.34/0.73    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 2.34/0.73    introduced(choice_axiom,[])).
% 2.34/0.73  fof(f14,plain,(
% 2.34/0.73    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.34/0.73    inference(flattening,[],[f13])).
% 2.34/0.73  fof(f13,plain,(
% 2.34/0.73    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.34/0.73    inference(ennf_transformation,[],[f12])).
% 2.34/0.73  fof(f12,negated_conjecture,(
% 2.34/0.73    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.34/0.73    inference(negated_conjecture,[],[f11])).
% 2.34/0.73  fof(f11,conjecture,(
% 2.34/0.73    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.34/0.73  fof(f1680,plain,(
% 2.34/0.73    r1_tarski(sK2,sK4) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(superposition,[],[f525,f1651])).
% 2.34/0.73  fof(f1651,plain,(
% 2.34/0.73    sK2 = k3_xboole_0(sK2,sK4) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(resolution,[],[f1639,f382])).
% 2.34/0.73  fof(f382,plain,(
% 2.34/0.73    ( ! [X6,X7] : (~r1_tarski(X6,k3_xboole_0(X6,X7)) | k3_xboole_0(X6,X7) = X6) )),
% 2.34/0.73    inference(resolution,[],[f379,f45])).
% 2.34/0.73  fof(f45,plain,(
% 2.34/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.34/0.73    inference(cnf_transformation,[],[f24])).
% 2.34/0.73  fof(f24,plain,(
% 2.34/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.73    inference(flattening,[],[f23])).
% 2.34/0.73  fof(f23,plain,(
% 2.34/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.73    inference(nnf_transformation,[],[f3])).
% 2.34/0.73  fof(f3,axiom,(
% 2.34/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.34/0.73  fof(f379,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.34/0.73    inference(duplicate_literal_removal,[],[f369])).
% 2.34/0.73  fof(f369,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.34/0.73    inference(resolution,[],[f258,f48])).
% 2.34/0.73  fof(f48,plain,(
% 2.34/0.73    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f28])).
% 2.34/0.73  fof(f28,plain,(
% 2.34/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 2.34/0.73  fof(f27,plain,(
% 2.34/0.73    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.34/0.73    introduced(choice_axiom,[])).
% 2.34/0.73  fof(f26,plain,(
% 2.34/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.73    inference(rectify,[],[f25])).
% 2.34/0.73  fof(f25,plain,(
% 2.34/0.73    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.73    inference(nnf_transformation,[],[f16])).
% 2.34/0.73  fof(f16,plain,(
% 2.34/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.34/0.73    inference(ennf_transformation,[],[f1])).
% 2.34/0.73  fof(f1,axiom,(
% 2.34/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.34/0.73  fof(f258,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.34/0.73    inference(resolution,[],[f139,f71])).
% 2.34/0.73  fof(f71,plain,(
% 2.34/0.73    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 2.34/0.73    inference(equality_resolution,[],[f62])).
% 2.34/0.73  fof(f62,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.34/0.73    inference(cnf_transformation,[],[f37])).
% 2.34/0.73  fof(f37,plain,(
% 2.34/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.34/0.73    inference(nnf_transformation,[],[f20])).
% 2.34/0.73  fof(f20,plain,(
% 2.34/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.34/0.73    inference(definition_folding,[],[f2,f19])).
% 2.34/0.73  fof(f19,plain,(
% 2.34/0.73    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.34/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.34/0.73  fof(f2,axiom,(
% 2.34/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.34/0.73  fof(f139,plain,(
% 2.34/0.73    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(resolution,[],[f56,f47])).
% 2.34/0.73  fof(f47,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f28])).
% 2.34/0.73  fof(f56,plain,(
% 2.34/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f36])).
% 2.34/0.73  fof(f36,plain,(
% 2.34/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.34/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 2.34/0.73  fof(f35,plain,(
% 2.34/0.73    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.34/0.73    introduced(choice_axiom,[])).
% 2.34/0.73  fof(f34,plain,(
% 2.34/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.34/0.73    inference(rectify,[],[f33])).
% 2.34/0.73  fof(f33,plain,(
% 2.34/0.73    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.34/0.73    inference(flattening,[],[f32])).
% 2.34/0.73  fof(f32,plain,(
% 2.34/0.73    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.34/0.73    inference(nnf_transformation,[],[f19])).
% 2.34/0.73  fof(f1639,plain,(
% 2.34/0.73    r1_tarski(sK2,k3_xboole_0(sK2,sK4)) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(resolution,[],[f1610,f65])).
% 2.34/0.73  fof(f65,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.34/0.73    inference(cnf_transformation,[],[f18])).
% 2.34/0.73  fof(f18,plain,(
% 2.34/0.73    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 2.34/0.73    inference(ennf_transformation,[],[f8])).
% 2.34/0.73  fof(f8,axiom,(
% 2.34/0.73    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 2.34/0.73  fof(f1610,plain,(
% 2.34/0.73    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)))),
% 2.34/0.73    inference(superposition,[],[f1094,f73])).
% 2.34/0.73  fof(f73,plain,(
% 2.34/0.73    k2_zfmisc_1(sK1,sK2) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.34/0.73    inference(resolution,[],[f42,f38])).
% 2.34/0.73  fof(f38,plain,(
% 2.34/0.73    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 2.34/0.73    inference(cnf_transformation,[],[f22])).
% 2.34/0.73  fof(f42,plain,(
% 2.34/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.34/0.73    inference(cnf_transformation,[],[f15])).
% 2.34/0.73  fof(f15,plain,(
% 2.34/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.34/0.73    inference(ennf_transformation,[],[f5])).
% 2.34/0.73  fof(f5,axiom,(
% 2.34/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.34/0.73  fof(f1094,plain,(
% 2.34/0.73    ( ! [X14,X12,X15,X13] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)),k2_zfmisc_1(X12,k3_xboole_0(X14,X15)))) )),
% 2.34/0.73    inference(superposition,[],[f381,f66])).
% 2.34/0.73  fof(f66,plain,(
% 2.34/0.73    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.34/0.73    inference(cnf_transformation,[],[f10])).
% 2.34/0.73  fof(f10,axiom,(
% 2.34/0.73    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.34/0.73  fof(f381,plain,(
% 2.34/0.73    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X3,X5))) )),
% 2.34/0.73    inference(resolution,[],[f379,f54])).
% 2.34/0.73  fof(f54,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.34/0.73    inference(cnf_transformation,[],[f17])).
% 2.34/0.73  fof(f17,plain,(
% 2.34/0.73    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 2.34/0.73    inference(ennf_transformation,[],[f9])).
% 2.34/0.73  fof(f9,axiom,(
% 2.34/0.73    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 2.34/0.73  fof(f525,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.34/0.73    inference(duplicate_literal_removal,[],[f514])).
% 2.34/0.73  fof(f514,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.34/0.73    inference(resolution,[],[f305,f48])).
% 2.34/0.73  fof(f305,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 2.34/0.73    inference(resolution,[],[f140,f71])).
% 2.34/0.73  fof(f140,plain,(
% 2.34/0.73    ( ! [X2,X0,X3,X1] : (~sP0(X2,X3,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(resolution,[],[f57,f47])).
% 2.34/0.73  fof(f57,plain,(
% 2.34/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f36])).
% 2.34/0.73  fof(f1720,plain,(
% 2.34/0.73    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 2.34/0.73    inference(resolution,[],[f1699,f64])).
% 2.34/0.73  fof(f64,plain,(
% 2.34/0.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.34/0.73    inference(cnf_transformation,[],[f18])).
% 2.34/0.73  fof(f1699,plain,(
% 2.34/0.73    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))),
% 2.34/0.73    inference(subsumption_resolution,[],[f1659,f328])).
% 2.34/0.73  fof(f328,plain,(
% 2.34/0.73    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) | k1_xboole_0 != X3) )),
% 2.34/0.73    inference(resolution,[],[f321,f54])).
% 2.34/0.73  fof(f321,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != X0) )),
% 2.34/0.73    inference(duplicate_literal_removal,[],[f317])).
% 2.34/0.73  fof(f317,plain,(
% 2.34/0.73    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,X1) | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(resolution,[],[f316,f48])).
% 2.34/0.73  fof(f316,plain,(
% 2.34/0.73    ( ! [X10,X11,X9] : (r2_hidden(sK5(X9,X10),X11) | k1_xboole_0 != X9 | r1_tarski(X9,X10)) )),
% 2.34/0.73    inference(subsumption_resolution,[],[f314,f267])).
% 2.34/0.73  fof(f267,plain,(
% 2.34/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.34/0.73    inference(duplicate_literal_removal,[],[f263])).
% 2.34/0.73  fof(f263,plain,(
% 2.34/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 2.34/0.73    inference(resolution,[],[f260,f48])).
% 2.34/0.73  fof(f260,plain,(
% 2.34/0.73    ( ! [X6,X5] : (r2_hidden(sK5(k1_xboole_0,X5),X6) | r1_tarski(k1_xboole_0,X5)) )),
% 2.34/0.73    inference(resolution,[],[f139,f88])).
% 2.34/0.73  fof(f88,plain,(
% 2.34/0.73    ( ! [X0] : (sP0(k1_xboole_0,X0,k1_xboole_0)) )),
% 2.34/0.73    inference(superposition,[],[f71,f87])).
% 2.34/0.73  fof(f87,plain,(
% 2.34/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.34/0.73    inference(forward_demodulation,[],[f85,f77])).
% 2.34/0.73  fof(f77,plain,(
% 2.34/0.73    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.34/0.73    inference(resolution,[],[f53,f67])).
% 2.34/0.73  fof(f67,plain,(
% 2.34/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.34/0.73    inference(equality_resolution,[],[f44])).
% 2.34/0.73  fof(f44,plain,(
% 2.34/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.34/0.73    inference(cnf_transformation,[],[f24])).
% 2.34/0.73  fof(f53,plain,(
% 2.34/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.34/0.73    inference(cnf_transformation,[],[f31])).
% 2.34/0.73  fof(f31,plain,(
% 2.34/0.73    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.34/0.73    inference(nnf_transformation,[],[f4])).
% 2.34/0.73  fof(f4,axiom,(
% 2.34/0.73    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.34/0.73  fof(f85,plain,(
% 2.34/0.73    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.34/0.73    inference(superposition,[],[f41,f84])).
% 2.34/0.73  fof(f84,plain,(
% 2.34/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.34/0.73    inference(forward_demodulation,[],[f81,f72])).
% 2.34/0.73  fof(f72,plain,(
% 2.34/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.34/0.73    inference(resolution,[],[f42,f67])).
% 2.34/0.73  fof(f81,plain,(
% 2.34/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.34/0.73    inference(superposition,[],[f41,f77])).
% 2.34/0.73  fof(f41,plain,(
% 2.34/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.34/0.73    inference(cnf_transformation,[],[f6])).
% 2.34/0.73  fof(f6,axiom,(
% 2.34/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.34/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.34/0.73  fof(f314,plain,(
% 2.34/0.73    ( ! [X10,X11,X9] : (r1_tarski(X9,X10) | k1_xboole_0 != X9 | r2_hidden(sK5(X9,X10),X11) | ~r1_tarski(k1_xboole_0,X11)) )),
% 2.34/0.73    inference(resolution,[],[f309,f46])).
% 2.34/0.73  fof(f46,plain,(
% 2.34/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f28])).
% 2.34/0.73  fof(f309,plain,(
% 2.34/0.73    ( ! [X8,X9] : (r2_hidden(sK5(X8,X9),k1_xboole_0) | r1_tarski(X8,X9) | k1_xboole_0 != X8) )),
% 2.34/0.73    inference(resolution,[],[f140,f94])).
% 2.34/0.73  fof(f94,plain,(
% 2.34/0.73    ( ! [X1] : (sP0(k1_xboole_0,X1,X1) | k1_xboole_0 != X1) )),
% 2.34/0.73    inference(superposition,[],[f71,f90])).
% 2.34/0.73  fof(f90,plain,(
% 2.34/0.73    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = X1 | k1_xboole_0 != X1) )),
% 2.34/0.73    inference(resolution,[],[f86,f42])).
% 2.34/0.73  fof(f86,plain,(
% 2.34/0.73    ( ! [X1] : (r1_tarski(X1,k1_xboole_0) | k1_xboole_0 != X1) )),
% 2.34/0.73    inference(superposition,[],[f52,f84])).
% 2.34/0.73  fof(f52,plain,(
% 2.34/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.34/0.73    inference(cnf_transformation,[],[f31])).
% 2.34/0.73  fof(f1659,plain,(
% 2.34/0.73    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) | k1_xboole_0 = sK1),
% 2.34/0.73    inference(superposition,[],[f1549,f1651])).
% 2.34/0.73  fof(f1549,plain,(
% 2.34/0.73    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))),
% 2.34/0.73    inference(superposition,[],[f1092,f73])).
% 2.34/0.73  fof(f1092,plain,(
% 2.34/0.73    ( ! [X6,X4,X7,X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(X5,k3_xboole_0(X6,X7)))) )),
% 2.34/0.73    inference(superposition,[],[f527,f66])).
% 2.34/0.73  fof(f527,plain,(
% 2.34/0.73    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X3,X4),X5),k2_zfmisc_1(X4,X5))) )),
% 2.34/0.73    inference(resolution,[],[f525,f54])).
% 2.34/0.73  fof(f39,plain,(
% 2.34/0.73    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 2.34/0.73    inference(cnf_transformation,[],[f22])).
% 2.34/0.73  % SZS output end Proof for theBenchmark
% 2.34/0.73  % (5460)------------------------------
% 2.34/0.73  % (5460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.73  % (5460)Termination reason: Refutation
% 2.34/0.73  
% 2.34/0.73  % (5460)Memory used [KB]: 7547
% 2.34/0.73  % (5460)Time elapsed: 0.293 s
% 2.34/0.73  % (5460)------------------------------
% 2.34/0.73  % (5460)------------------------------
% 2.34/0.73  % (5452)Success in time 0.37 s
%------------------------------------------------------------------------------
