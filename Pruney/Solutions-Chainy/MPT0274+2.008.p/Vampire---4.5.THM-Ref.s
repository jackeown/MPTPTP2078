%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:21 EST 2020

% Result     : Theorem 4.56s
% Output     : Refutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 617 expanded)
%              Number of leaves         :   22 ( 193 expanded)
%              Depth                    :   26
%              Number of atoms          :  286 (1169 expanded)
%              Number of equality atoms :  146 ( 740 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7023,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7020,f153])).

fof(f153,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f149,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f149,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f113,f112])).

fof(f112,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f113,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f7020,plain,(
    ~ r2_hidden(sK1,k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f7019,f6831])).

fof(f6831,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X7,k2_tarski(sK1,sK2)) ) ),
    inference(superposition,[],[f5331,f6810])).

fof(f6810,plain,(
    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f6809,f62])).

fof(f62,plain,
    ( ~ r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( r2_hidden(sK2,sK3)
      | r2_hidden(sK1,sK3)
      | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
    & ( ( ~ r2_hidden(sK2,sK3)
        & ~ r2_hidden(sK1,sK3) )
      | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK2,sK3)
        | r2_hidden(sK1,sK3)
        | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
      & ( ( ~ r2_hidden(sK2,sK3)
          & ~ r2_hidden(sK1,sK3) )
        | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f6809,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f63,f5377])).

fof(f5377,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f64,f5368])).

fof(f5368,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(backward_demodulation,[],[f4849,f5327])).

fof(f5327,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X34,k2_xboole_0(X33,X34)) ),
    inference(forward_demodulation,[],[f5285,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f5285,plain,(
    ! [X33,X34] : k5_xboole_0(X34,k2_xboole_0(X33,X34)) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(superposition,[],[f898,f883])).

fof(f883,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f89,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f89,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f898,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f875,f119])).

fof(f119,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f875,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f89,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f4849,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1)) ) ),
    inference(resolution,[],[f95,f1679])).

fof(f1679,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f84,f1674])).

fof(f1674,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f1664,f72])).

fof(f1664,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(k2_xboole_0(X3,X4),X4) ),
    inference(superposition,[],[f76,f1621])).

fof(f1621,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f1582,f172])).

fof(f172,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f143,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f143,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f75,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1582,plain,(
    ! [X6,X7] : k3_xboole_0(k2_xboole_0(X6,X7),X6) = X6 ),
    inference(forward_demodulation,[],[f1540,f925])).

fof(f925,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f902,f902])).

fof(f902,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f898,f72])).

fof(f1540,plain,(
    ! [X6,X7] : k3_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f79,f1114])).

fof(f1114,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f1098,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1098,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k2_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f77,f1030])).

fof(f1030,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1024,f65])).

fof(f1024,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f76,f940])).

fof(f940,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f792,f924])).

fof(f924,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f902,f898])).

fof(f792,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f64,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f5331,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k4_xboole_0(X4,X3))
      | ~ r2_hidden(X2,X3) ) ),
    inference(backward_demodulation,[],[f1210,f5327])).

fof(f1210,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,k5_xboole_0(X3,k2_xboole_0(X4,X3)))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f1076,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (10754)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1076,plain,(
    ! [X2,X1] : r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(superposition,[],[f1023,f172])).

fof(f1023,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f73,f940])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f7019,plain,(
    r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f7012,f154])).

fof(f154,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f153,f71])).

fof(f7012,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f6831,f5377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:22:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (10691)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (10702)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (10708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (10699)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (10688)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10689)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (10694)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (10690)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10693)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (10692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10703)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (10712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10698)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (10700)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (10697)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (10695)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (10704)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (10709)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (10710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (10696)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (10717)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (10715)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (10713)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (10714)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (10696)Refutation not found, incomplete strategy% (10696)------------------------------
% 0.22/0.56  % (10696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10696)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10696)Memory used [KB]: 10746
% 0.22/0.56  % (10696)Time elapsed: 0.149 s
% 0.22/0.56  % (10696)------------------------------
% 0.22/0.56  % (10696)------------------------------
% 0.22/0.56  % (10716)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (10707)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (10701)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (10706)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (10705)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 3.19/0.79  % (10721)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.19/0.82  % (10693)Time limit reached!
% 3.19/0.82  % (10693)------------------------------
% 3.19/0.82  % (10693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.83  % (10693)Termination reason: Time limit
% 3.19/0.83  
% 3.19/0.83  % (10693)Memory used [KB]: 9210
% 3.19/0.83  % (10693)Time elapsed: 0.408 s
% 3.19/0.83  % (10693)------------------------------
% 3.19/0.83  % (10693)------------------------------
% 3.84/0.92  % (10698)Time limit reached!
% 3.84/0.92  % (10698)------------------------------
% 3.84/0.92  % (10698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.92  % (10698)Termination reason: Time limit
% 3.84/0.92  % (10698)Termination phase: Saturation
% 3.84/0.92  
% 3.84/0.92  % (10698)Memory used [KB]: 14711
% 3.84/0.92  % (10698)Time elapsed: 0.500 s
% 3.84/0.92  % (10698)------------------------------
% 3.84/0.92  % (10698)------------------------------
% 3.84/0.92  % (10700)Time limit reached!
% 3.84/0.92  % (10700)------------------------------
% 3.84/0.92  % (10700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.92  % (10700)Termination reason: Time limit
% 3.84/0.92  
% 3.84/0.92  % (10700)Memory used [KB]: 7419
% 3.84/0.92  % (10700)Time elapsed: 0.506 s
% 3.84/0.92  % (10700)------------------------------
% 3.84/0.92  % (10700)------------------------------
% 4.28/0.93  % (10705)Time limit reached!
% 4.28/0.93  % (10705)------------------------------
% 4.28/0.93  % (10705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.93  % (10705)Termination reason: Time limit
% 4.28/0.93  % (10705)Termination phase: Saturation
% 4.28/0.93  
% 4.28/0.93  % (10705)Memory used [KB]: 14200
% 4.28/0.93  % (10705)Time elapsed: 0.520 s
% 4.28/0.93  % (10705)------------------------------
% 4.28/0.93  % (10705)------------------------------
% 4.28/0.95  % (10689)Time limit reached!
% 4.28/0.95  % (10689)------------------------------
% 4.28/0.95  % (10689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.95  % (10689)Termination reason: Time limit
% 4.28/0.95  
% 4.28/0.95  % (10689)Memory used [KB]: 8187
% 4.28/0.95  % (10689)Time elapsed: 0.505 s
% 4.28/0.95  % (10689)------------------------------
% 4.28/0.95  % (10689)------------------------------
% 4.28/0.95  % (10688)Time limit reached!
% 4.28/0.95  % (10688)------------------------------
% 4.28/0.95  % (10688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.95  % (10688)Termination reason: Time limit
% 4.28/0.95  
% 4.28/0.95  % (10688)Memory used [KB]: 2302
% 4.28/0.95  % (10688)Time elapsed: 0.534 s
% 4.28/0.95  % (10688)------------------------------
% 4.28/0.95  % (10688)------------------------------
% 4.56/0.96  % (10695)Refutation found. Thanks to Tanya!
% 4.56/0.96  % SZS status Theorem for theBenchmark
% 4.56/0.96  % SZS output start Proof for theBenchmark
% 4.56/0.96  fof(f7023,plain,(
% 4.56/0.96    $false),
% 4.56/0.96    inference(subsumption_resolution,[],[f7020,f153])).
% 4.56/0.96  fof(f153,plain,(
% 4.56/0.96    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 4.56/0.96    inference(superposition,[],[f149,f74])).
% 4.56/0.96  fof(f74,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f22])).
% 4.56/0.96  fof(f22,axiom,(
% 4.56/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.56/0.96  fof(f149,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 4.56/0.96    inference(resolution,[],[f113,f112])).
% 4.56/0.96  fof(f112,plain,(
% 4.56/0.96    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 4.56/0.96    inference(equality_resolution,[],[f98])).
% 4.56/0.96  fof(f98,plain,(
% 4.56/0.96    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f60])).
% 4.56/0.96  fof(f60,plain,(
% 4.56/0.96    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 4.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 4.56/0.96  fof(f59,plain,(
% 4.56/0.96    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 4.56/0.96    introduced(choice_axiom,[])).
% 4.56/0.96  fof(f58,plain,(
% 4.56/0.96    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 4.56/0.96    inference(rectify,[],[f57])).
% 4.56/0.96  fof(f57,plain,(
% 4.56/0.96    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 4.56/0.96    inference(flattening,[],[f56])).
% 4.56/0.96  fof(f56,plain,(
% 4.56/0.96    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 4.56/0.96    inference(nnf_transformation,[],[f43])).
% 4.56/0.96  fof(f43,plain,(
% 4.56/0.96    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.56/0.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.56/0.96  fof(f113,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 4.56/0.96    inference(equality_resolution,[],[f105])).
% 4.56/0.96  fof(f105,plain,(
% 4.56/0.96    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.56/0.96    inference(cnf_transformation,[],[f61])).
% 4.56/0.96  fof(f61,plain,(
% 4.56/0.96    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 4.56/0.96    inference(nnf_transformation,[],[f44])).
% 4.56/0.96  fof(f44,plain,(
% 4.56/0.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 4.56/0.96    inference(definition_folding,[],[f42,f43])).
% 4.56/0.96  fof(f42,plain,(
% 4.56/0.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.56/0.96    inference(ennf_transformation,[],[f21])).
% 4.56/0.96  fof(f21,axiom,(
% 4.56/0.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 4.56/0.96  fof(f7020,plain,(
% 4.56/0.96    ~r2_hidden(sK1,k2_tarski(sK1,sK2))),
% 4.56/0.96    inference(resolution,[],[f7019,f6831])).
% 4.56/0.96  fof(f6831,plain,(
% 4.56/0.96    ( ! [X7] : (~r2_hidden(X7,sK3) | ~r2_hidden(X7,k2_tarski(sK1,sK2))) )),
% 4.56/0.96    inference(superposition,[],[f5331,f6810])).
% 4.56/0.96  fof(f6810,plain,(
% 4.56/0.96    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 4.56/0.96    inference(subsumption_resolution,[],[f6809,f62])).
% 4.56/0.96  fof(f62,plain,(
% 4.56/0.96    ~r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 4.56/0.96    inference(cnf_transformation,[],[f48])).
% 4.56/0.96  fof(f48,plain,(
% 4.56/0.96    (r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3)) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3))),
% 4.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f47])).
% 4.56/0.96  fof(f47,plain,(
% 4.56/0.96    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3)) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)))),
% 4.56/0.96    introduced(choice_axiom,[])).
% 4.56/0.96  fof(f46,plain,(
% 4.56/0.96    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.56/0.96    inference(flattening,[],[f45])).
% 4.56/0.96  fof(f45,plain,(
% 4.56/0.96    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.56/0.96    inference(nnf_transformation,[],[f35])).
% 4.56/0.96  fof(f35,plain,(
% 4.56/0.96    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.56/0.96    inference(ennf_transformation,[],[f31])).
% 4.56/0.96  fof(f31,negated_conjecture,(
% 4.56/0.96    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.56/0.96    inference(negated_conjecture,[],[f30])).
% 4.56/0.96  fof(f30,conjecture,(
% 4.56/0.96    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 4.56/0.96  fof(f6809,plain,(
% 4.56/0.96    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) | r2_hidden(sK1,sK3)),
% 4.56/0.96    inference(resolution,[],[f63,f5377])).
% 4.56/0.96  fof(f5377,plain,(
% 4.56/0.96    r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3)),
% 4.56/0.96    inference(subsumption_resolution,[],[f64,f5368])).
% 4.56/0.96  fof(f5368,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) | r2_hidden(X0,X1) | r2_hidden(X2,X1)) )),
% 4.56/0.96    inference(backward_demodulation,[],[f4849,f5327])).
% 4.56/0.96  fof(f5327,plain,(
% 4.56/0.96    ( ! [X33,X34] : (k4_xboole_0(X33,X34) = k5_xboole_0(X34,k2_xboole_0(X33,X34))) )),
% 4.56/0.96    inference(forward_demodulation,[],[f5285,f76])).
% 4.56/0.96  fof(f76,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f8])).
% 4.56/0.96  fof(f8,axiom,(
% 4.56/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.56/0.96  fof(f5285,plain,(
% 4.56/0.96    ( ! [X33,X34] : (k5_xboole_0(X34,k2_xboole_0(X33,X34)) = k5_xboole_0(X33,k3_xboole_0(X33,X34))) )),
% 4.56/0.96    inference(superposition,[],[f898,f883])).
% 4.56/0.96  fof(f883,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 4.56/0.96    inference(superposition,[],[f89,f79])).
% 4.56/0.96  fof(f79,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f19])).
% 4.56/0.96  fof(f19,axiom,(
% 4.56/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.56/0.96  fof(f89,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f17])).
% 4.56/0.96  fof(f17,axiom,(
% 4.56/0.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.56/0.96  fof(f898,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.56/0.96    inference(forward_demodulation,[],[f875,f119])).
% 4.56/0.96  fof(f119,plain,(
% 4.56/0.96    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 4.56/0.96    inference(superposition,[],[f72,f66])).
% 4.56/0.96  fof(f66,plain,(
% 4.56/0.96    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.56/0.96    inference(cnf_transformation,[],[f13])).
% 4.56/0.96  fof(f13,axiom,(
% 4.56/0.96    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 4.56/0.96  fof(f72,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f1])).
% 4.56/0.96  fof(f1,axiom,(
% 4.56/0.96    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.56/0.96  fof(f875,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.56/0.96    inference(superposition,[],[f89,f65])).
% 4.56/0.96  fof(f65,plain,(
% 4.56/0.96    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f18])).
% 4.56/0.96  fof(f18,axiom,(
% 4.56/0.96    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.56/0.96  fof(f4849,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1))) )),
% 4.56/0.96    inference(resolution,[],[f95,f1679])).
% 4.56/0.96  fof(f1679,plain,(
% 4.56/0.96    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0) )),
% 4.56/0.96    inference(backward_demodulation,[],[f84,f1674])).
% 4.56/0.96  fof(f1674,plain,(
% 4.56/0.96    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 4.56/0.96    inference(forward_demodulation,[],[f1664,f72])).
% 4.56/0.96  fof(f1664,plain,(
% 4.56/0.96    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(k2_xboole_0(X3,X4),X4)) )),
% 4.56/0.96    inference(superposition,[],[f76,f1621])).
% 4.56/0.96  fof(f1621,plain,(
% 4.56/0.96    ( ! [X2,X1] : (k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1) )),
% 4.56/0.96    inference(superposition,[],[f1582,f172])).
% 4.56/0.96  fof(f172,plain,(
% 4.56/0.96    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 4.56/0.96    inference(superposition,[],[f143,f75])).
% 4.56/0.96  fof(f75,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f28])).
% 4.56/0.96  fof(f28,axiom,(
% 4.56/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.56/0.96  fof(f143,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 4.56/0.96    inference(superposition,[],[f75,f71])).
% 4.56/0.96  fof(f71,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f20])).
% 4.56/0.96  fof(f20,axiom,(
% 4.56/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.56/0.96  fof(f1582,plain,(
% 4.56/0.96    ( ! [X6,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),X6) = X6) )),
% 4.56/0.96    inference(forward_demodulation,[],[f1540,f925])).
% 4.56/0.96  fof(f925,plain,(
% 4.56/0.96    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.56/0.96    inference(superposition,[],[f902,f902])).
% 4.56/0.96  fof(f902,plain,(
% 4.56/0.96    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.56/0.96    inference(superposition,[],[f898,f72])).
% 4.56/0.96  fof(f1540,plain,(
% 4.56/0.96    ( ! [X6,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),k2_xboole_0(X6,X7))) )),
% 4.56/0.96    inference(superposition,[],[f79,f1114])).
% 4.56/0.96  fof(f1114,plain,(
% 4.56/0.96    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2)) )),
% 4.56/0.96    inference(forward_demodulation,[],[f1098,f67])).
% 4.56/0.96  fof(f67,plain,(
% 4.56/0.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.56/0.96    inference(cnf_transformation,[],[f10])).
% 4.56/0.96  fof(f10,axiom,(
% 4.56/0.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 4.56/0.96  fof(f1098,plain,(
% 4.56/0.96    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k2_xboole_0(X2,X3),k1_xboole_0)) )),
% 4.56/0.96    inference(superposition,[],[f77,f1030])).
% 4.56/0.96  fof(f1030,plain,(
% 4.56/0.96    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 4.56/0.96    inference(forward_demodulation,[],[f1024,f65])).
% 4.56/0.96  fof(f1024,plain,(
% 4.56/0.96    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k5_xboole_0(X2,X2)) )),
% 4.56/0.96    inference(superposition,[],[f76,f940])).
% 4.56/0.96  fof(f940,plain,(
% 4.56/0.96    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 4.56/0.96    inference(backward_demodulation,[],[f792,f924])).
% 4.56/0.96  fof(f924,plain,(
% 4.56/0.96    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 4.56/0.96    inference(superposition,[],[f902,f898])).
% 4.56/0.96  fof(f792,plain,(
% 4.56/0.96    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 4.56/0.96    inference(superposition,[],[f79,f78])).
% 4.56/0.96  fof(f78,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f14])).
% 4.56/0.96  fof(f14,axiom,(
% 4.56/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 4.56/0.96  fof(f77,plain,(
% 4.56/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.56/0.96    inference(cnf_transformation,[],[f11])).
% 4.56/0.96  fof(f11,axiom,(
% 4.56/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.56/0.96  fof(f84,plain,(
% 4.56/0.96    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 4.56/0.96    inference(cnf_transformation,[],[f38])).
% 4.56/0.96  fof(f38,plain,(
% 4.56/0.96    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.56/0.96    inference(ennf_transformation,[],[f16])).
% 4.56/0.96  fof(f16,axiom,(
% 4.56/0.96    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 4.56/0.96  fof(f95,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f41])).
% 4.56/0.96  fof(f41,plain,(
% 4.56/0.96    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 4.56/0.96    inference(ennf_transformation,[],[f29])).
% 4.56/0.96  fof(f29,axiom,(
% 4.56/0.96    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 4.56/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 4.56/0.96  fof(f64,plain,(
% 4.56/0.96    r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 4.56/0.96    inference(cnf_transformation,[],[f48])).
% 4.56/0.96  fof(f63,plain,(
% 4.56/0.96    ~r2_hidden(sK2,sK3) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 4.56/0.96    inference(cnf_transformation,[],[f48])).
% 4.56/0.96  fof(f5331,plain,(
% 4.56/0.96    ( ! [X4,X2,X3] : (~r2_hidden(X2,k4_xboole_0(X4,X3)) | ~r2_hidden(X2,X3)) )),
% 4.56/0.96    inference(backward_demodulation,[],[f1210,f5327])).
% 4.56/0.96  fof(f1210,plain,(
% 4.56/0.96    ( ! [X4,X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k2_xboole_0(X4,X3))) | ~r2_hidden(X2,X3)) )),
% 4.56/0.96    inference(resolution,[],[f1076,f82])).
% 4.56/0.96  fof(f82,plain,(
% 4.56/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.56/0.96    inference(cnf_transformation,[],[f50])).
% 4.56/0.96  fof(f50,plain,(
% 4.56/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.56/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f49])).
% 4.56/0.96  fof(f49,plain,(
% 4.56/0.96    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 4.56/0.96    introduced(choice_axiom,[])).
% 4.56/0.96  % (10754)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.56/0.97  fof(f36,plain,(
% 4.56/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.56/0.97    inference(ennf_transformation,[],[f34])).
% 4.56/0.97  fof(f34,plain,(
% 4.56/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.56/0.97    inference(rectify,[],[f6])).
% 4.56/0.97  fof(f6,axiom,(
% 4.56/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.56/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.56/0.97  fof(f1076,plain,(
% 4.56/0.97    ( ! [X2,X1] : (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))) )),
% 4.56/0.97    inference(superposition,[],[f1023,f172])).
% 4.56/0.97  fof(f1023,plain,(
% 4.56/0.97    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 4.56/0.97    inference(superposition,[],[f73,f940])).
% 4.56/0.97  fof(f73,plain,(
% 4.56/0.97    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 4.56/0.97    inference(cnf_transformation,[],[f7])).
% 4.56/0.97  fof(f7,axiom,(
% 4.56/0.97    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 4.56/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 4.56/0.97  fof(f7019,plain,(
% 4.56/0.97    r2_hidden(sK1,sK3)),
% 4.56/0.97    inference(subsumption_resolution,[],[f7012,f154])).
% 4.56/0.97  fof(f154,plain,(
% 4.56/0.97    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 4.56/0.97    inference(superposition,[],[f153,f71])).
% 4.56/0.97  fof(f7012,plain,(
% 4.56/0.97    ~r2_hidden(sK2,k2_tarski(sK1,sK2)) | r2_hidden(sK1,sK3)),
% 4.56/0.97    inference(resolution,[],[f6831,f5377])).
% 4.56/0.97  % SZS output end Proof for theBenchmark
% 4.56/0.97  % (10695)------------------------------
% 4.56/0.97  % (10695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/0.97  % (10695)Termination reason: Refutation
% 4.56/0.97  
% 4.56/0.97  % (10695)Memory used [KB]: 9978
% 4.56/0.97  % (10695)Time elapsed: 0.510 s
% 4.56/0.97  % (10695)------------------------------
% 4.56/0.97  % (10695)------------------------------
% 4.56/0.97  % (10687)Success in time 0.603 s
%------------------------------------------------------------------------------
