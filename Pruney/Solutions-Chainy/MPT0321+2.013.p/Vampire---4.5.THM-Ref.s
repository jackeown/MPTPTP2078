%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:30 EST 2020

% Result     : Theorem 4.48s
% Output     : Refutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  126 (3357 expanded)
%              Number of leaves         :   15 ( 866 expanded)
%              Depth                    :   32
%              Number of atoms          :  320 (12531 expanded)
%              Number of equality atoms :  105 (4793 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4701,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4697,f4401])).

fof(f4401,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f1545,f4161])).

fof(f4161,plain,(
    sK1 != sK3 ),
    inference(subsumption_resolution,[],[f51,f4160])).

fof(f4160,plain,(
    sK2 = sK4 ),
    inference(subsumption_resolution,[],[f1720,f4144])).

fof(f4144,plain,(
    r1_tarski(sK2,sK4) ),
    inference(superposition,[],[f148,f3589])).

fof(f3589,plain,(
    sK2 = k3_xboole_0(sK2,sK4) ),
    inference(resolution,[],[f3500,f144])).

fof(f144,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,k3_xboole_0(X9,X10))
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(resolution,[],[f140,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f140,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f125,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f114,f87])).

fof(f87,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f28])).

fof(f28,plain,(
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

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f3500,plain,(
    r1_tarski(sK2,k3_xboole_0(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f3460,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3460,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | r1_tarski(sK2,k3_xboole_0(sK2,sK4)) ),
    inference(superposition,[],[f3134,f3420])).

fof(f3420,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)) ),
    inference(forward_demodulation,[],[f3369,f48])).

fof(f48,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sK2 != sK4
      | sK1 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f20,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK2 != sK4
        | sK1 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f3369,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4)) ),
    inference(superposition,[],[f3137,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f3137,plain,(
    ! [X12] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,X12)) ),
    inference(forward_demodulation,[],[f3116,f669])).

fof(f669,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ),
    inference(superposition,[],[f82,f53])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f3116,plain,(
    ! [X12] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X12)) ),
    inference(backward_demodulation,[],[f1368,f3101])).

fof(f3101,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f3096,f144])).

fof(f3096,plain,(
    r1_tarski(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f1364,f83])).

fof(f1364,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2))
      | r1_tarski(X5,k3_xboole_0(sK1,sK3)) ) ),
    inference(backward_demodulation,[],[f1314,f1346])).

fof(f1346,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1344,f248])).

fof(f248,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(X0,sK4)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f219,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f219,plain,(
    ! [X4] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X4)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f142,f48])).

fof(f142,plain,(
    ! [X4,X5,X3] : r1_tarski(k2_zfmisc_1(X3,k3_xboole_0(X4,X5)),k2_zfmisc_1(X3,X4)) ),
    inference(resolution,[],[f140,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1344,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)) ),
    inference(resolution,[],[f1338,f58])).

fof(f1338,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(forward_demodulation,[],[f1334,f48])).

fof(f1334,plain,(
    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f1316,f53])).

fof(f1316,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(forward_demodulation,[],[f1315,f730])).

fof(f730,plain,(
    ! [X20] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X20)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X20)) ),
    inference(superposition,[],[f669,f48])).

fof(f1315,plain,(
    ! [X8] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(forward_demodulation,[],[f1294,f82])).

fof(f1294,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) ),
    inference(superposition,[],[f142,f1279])).

fof(f1279,plain,(
    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)) ),
    inference(forward_demodulation,[],[f1248,f54])).

fof(f1248,plain,(
    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)) ),
    inference(superposition,[],[f730,f674])).

fof(f674,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f82,f53])).

fof(f1314,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))
      | r1_tarski(X5,k3_xboole_0(sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f1291,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f1291,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))
      | r1_tarski(X5,k3_xboole_0(sK1,sK3))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f80,f1279])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1368,plain,(
    ! [X12] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12)) ),
    inference(backward_demodulation,[],[f1320,f1346])).

fof(f1320,plain,(
    ! [X12] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12)) ),
    inference(forward_demodulation,[],[f1319,f730])).

fof(f1319,plain,(
    ! [X12] : k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12)) ),
    inference(forward_demodulation,[],[f1300,f82])).

fof(f1300,plain,(
    ! [X12] : k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12)) ),
    inference(superposition,[],[f669,f1279])).

fof(f3134,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X6))
      | r1_tarski(sK2,X6) ) ),
    inference(forward_demodulation,[],[f3133,f3101])).

fof(f3133,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6))
      | r1_tarski(sK2,X6) ) ),
    inference(subsumption_resolution,[],[f3110,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f3110,plain,(
    ! [X6] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6))
      | r1_tarski(sK2,X6) ) ),
    inference(backward_demodulation,[],[f1352,f3101])).

fof(f1352,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6))
      | r1_tarski(sK2,X6)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3) ) ),
    inference(backward_demodulation,[],[f1292,f1346])).

fof(f1292,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6))
      | r1_tarski(sK2,X6)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f81,f1279])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f140,f54])).

fof(f1720,plain,
    ( ~ r1_tarski(sK2,sK4)
    | sK2 = sK4 ),
    inference(resolution,[],[f1716,f58])).

fof(f1716,plain,(
    r1_tarski(sK4,sK2) ),
    inference(subsumption_resolution,[],[f1710,f49])).

fof(f1710,plain,
    ( r1_tarski(sK4,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f1701,f81])).

fof(f1701,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f1544,f48])).

fof(f1544,plain,(
    ! [X2] : r1_tarski(k2_zfmisc_1(sK1,X2),k2_zfmisc_1(sK3,X2)) ),
    inference(resolution,[],[f1541,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1541,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f1535,f50])).

fof(f1535,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1484,f80])).

fof(f1484,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) ),
    inference(superposition,[],[f179,f1347])).

fof(f1347,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) ),
    inference(backward_demodulation,[],[f1279,f1346])).

fof(f179,plain,(
    ! [X6,X8,X7] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X6,X7),X8),k2_zfmisc_1(X7,X8)) ),
    inference(resolution,[],[f148,f70])).

fof(f51,plain,
    ( sK2 != sK4
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f1545,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f1541,f58])).

fof(f4697,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f3766,f83])).

fof(f3766,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(X4,sK2))
      | r1_tarski(sK3,X4) ) ),
    inference(backward_demodulation,[],[f1646,f3598])).

fof(f3598,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f1346,f3589])).

fof(f1646,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(X4,sK2))
      | r1_tarski(sK3,X4) ) ),
    inference(forward_demodulation,[],[f1578,f1565])).

fof(f1565,plain,(
    k2_zfmisc_1(sK3,sK2) = k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)) ),
    inference(backward_demodulation,[],[f568,f1546])).

fof(f1546,plain,(
    sK3 = k2_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f1541,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f568,plain,(
    k2_zfmisc_1(k2_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[],[f376,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f376,plain,(
    ! [X7] : k2_zfmisc_1(sK3,k2_xboole_0(sK4,X7)) = k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X7)) ),
    inference(superposition,[],[f69,f48])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1578,plain,(
    ! [X4] :
      ( r1_tarski(sK3,X4)
      | ~ r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2)) ) ),
    inference(backward_demodulation,[],[f618,f1546])).

fof(f618,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2))
      | r1_tarski(k2_xboole_0(sK1,sK3),X4) ) ),
    inference(subsumption_resolution,[],[f607,f50])).

fof(f607,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2))
      | r1_tarski(k2_xboole_0(sK1,sK3),X4)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f80,f568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (28921)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (28929)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (28922)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (28937)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (28938)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (28926)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (28931)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28945)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (28928)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (28930)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (28923)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (28942)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (28935)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (28947)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (28919)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (28939)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.56  % (28932)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.56  % (28920)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  % (28948)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.57  % (28936)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.57  % (28940)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.57  % (28933)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.57  % (28946)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.57  % (28927)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.58  % (28941)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.58  % (28943)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.58  % (28944)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.68/0.58  % (28936)Refutation not found, incomplete strategy% (28936)------------------------------
% 1.68/0.58  % (28936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (28936)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (28936)Memory used [KB]: 10618
% 1.68/0.58  % (28936)Time elapsed: 0.176 s
% 1.68/0.58  % (28936)------------------------------
% 1.68/0.58  % (28936)------------------------------
% 1.68/0.58  % (28924)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.68/0.59  % (28934)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.68/0.59  % (28925)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.67/0.76  % (28949)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.72/0.87  % (28924)Time limit reached!
% 3.72/0.87  % (28924)------------------------------
% 3.72/0.87  % (28924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.87  % (28924)Termination reason: Time limit
% 3.72/0.87  % (28924)Termination phase: Saturation
% 3.72/0.87  
% 3.72/0.87  % (28924)Memory used [KB]: 8699
% 3.72/0.87  % (28924)Time elapsed: 0.400 s
% 3.72/0.87  % (28924)------------------------------
% 3.72/0.87  % (28924)------------------------------
% 3.96/0.91  % (28919)Time limit reached!
% 3.96/0.91  % (28919)------------------------------
% 3.96/0.91  % (28919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.91  % (28931)Time limit reached!
% 3.96/0.91  % (28931)------------------------------
% 3.96/0.91  % (28931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.92  % (28931)Termination reason: Time limit
% 3.96/0.92  
% 3.96/0.92  % (28931)Memory used [KB]: 8955
% 3.96/0.92  % (28931)Time elapsed: 0.510 s
% 3.96/0.92  % (28931)------------------------------
% 3.96/0.92  % (28931)------------------------------
% 3.96/0.92  % (28919)Termination reason: Time limit
% 3.96/0.92  % (28919)Termination phase: Saturation
% 3.96/0.92  
% 3.96/0.92  % (28919)Memory used [KB]: 3070
% 3.96/0.92  % (28919)Time elapsed: 0.500 s
% 3.96/0.92  % (28919)------------------------------
% 3.96/0.92  % (28919)------------------------------
% 3.96/0.93  % (28929)Time limit reached!
% 3.96/0.93  % (28929)------------------------------
% 3.96/0.93  % (28929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.93  % (28929)Termination reason: Time limit
% 3.96/0.93  
% 3.96/0.93  % (28929)Memory used [KB]: 18421
% 3.96/0.93  % (28929)Time elapsed: 0.524 s
% 3.96/0.93  % (28929)------------------------------
% 3.96/0.93  % (28929)------------------------------
% 4.37/0.95  % (28920)Time limit reached!
% 4.37/0.95  % (28920)------------------------------
% 4.37/0.95  % (28920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.95  % (28920)Termination reason: Time limit
% 4.37/0.95  % (28920)Termination phase: Saturation
% 4.37/0.95  
% 4.37/0.95  % (28920)Memory used [KB]: 8955
% 4.37/0.95  % (28920)Time elapsed: 0.500 s
% 4.37/0.95  % (28920)------------------------------
% 4.37/0.95  % (28920)------------------------------
% 4.48/0.98  % (28926)Refutation found. Thanks to Tanya!
% 4.48/0.98  % SZS status Theorem for theBenchmark
% 4.48/0.99  % (28950)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.48/1.00  % SZS output start Proof for theBenchmark
% 4.48/1.00  fof(f4701,plain,(
% 4.48/1.00    $false),
% 4.48/1.00    inference(subsumption_resolution,[],[f4697,f4401])).
% 4.48/1.00  fof(f4401,plain,(
% 4.48/1.00    ~r1_tarski(sK3,sK1)),
% 4.48/1.00    inference(subsumption_resolution,[],[f1545,f4161])).
% 4.48/1.00  fof(f4161,plain,(
% 4.48/1.00    sK1 != sK3),
% 4.48/1.00    inference(subsumption_resolution,[],[f51,f4160])).
% 4.48/1.00  fof(f4160,plain,(
% 4.48/1.00    sK2 = sK4),
% 4.48/1.00    inference(subsumption_resolution,[],[f1720,f4144])).
% 4.48/1.00  fof(f4144,plain,(
% 4.48/1.00    r1_tarski(sK2,sK4)),
% 4.48/1.00    inference(superposition,[],[f148,f3589])).
% 4.48/1.00  fof(f3589,plain,(
% 4.48/1.00    sK2 = k3_xboole_0(sK2,sK4)),
% 4.48/1.00    inference(resolution,[],[f3500,f144])).
% 4.48/1.00  fof(f144,plain,(
% 4.48/1.00    ( ! [X10,X9] : (~r1_tarski(X9,k3_xboole_0(X9,X10)) | k3_xboole_0(X9,X10) = X9) )),
% 4.48/1.00    inference(resolution,[],[f140,f58])).
% 4.48/1.00  fof(f58,plain,(
% 4.48/1.00    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.48/1.00    inference(cnf_transformation,[],[f33])).
% 4.48/1.00  fof(f33,plain,(
% 4.48/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.48/1.00    inference(flattening,[],[f32])).
% 4.48/1.00  fof(f32,plain,(
% 4.48/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.48/1.00    inference(nnf_transformation,[],[f7])).
% 4.48/1.00  fof(f7,axiom,(
% 4.48/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.48/1.00  fof(f140,plain,(
% 4.48/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.48/1.00    inference(duplicate_literal_removal,[],[f133])).
% 4.48/1.00  fof(f133,plain,(
% 4.48/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.48/1.00    inference(resolution,[],[f125,f62])).
% 4.48/1.00  fof(f62,plain,(
% 4.48/1.00    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.48/1.00    inference(cnf_transformation,[],[f37])).
% 4.48/1.00  fof(f37,plain,(
% 4.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 4.48/1.00  fof(f36,plain,(
% 4.48/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 4.48/1.00    introduced(choice_axiom,[])).
% 4.48/1.00  fof(f35,plain,(
% 4.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.48/1.00    inference(rectify,[],[f34])).
% 4.48/1.00  fof(f34,plain,(
% 4.48/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.48/1.00    inference(nnf_transformation,[],[f24])).
% 4.48/1.00  fof(f24,plain,(
% 4.48/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.48/1.00    inference(ennf_transformation,[],[f2])).
% 4.48/1.00  fof(f2,axiom,(
% 4.48/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 4.48/1.00  fof(f125,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 4.48/1.00    inference(resolution,[],[f114,f87])).
% 4.48/1.00  fof(f87,plain,(
% 4.48/1.00    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 4.48/1.00    inference(equality_resolution,[],[f78])).
% 4.48/1.00  fof(f78,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 4.48/1.00    inference(cnf_transformation,[],[f47])).
% 4.48/1.00  fof(f47,plain,(
% 4.48/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 4.48/1.00    inference(nnf_transformation,[],[f29])).
% 4.48/1.00  fof(f29,plain,(
% 4.48/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 4.48/1.00    inference(definition_folding,[],[f3,f28])).
% 4.48/1.00  fof(f28,plain,(
% 4.48/1.00    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.48/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.48/1.00  fof(f3,axiom,(
% 4.48/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 4.48/1.00  fof(f114,plain,(
% 4.48/1.00    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 4.48/1.00    inference(resolution,[],[f72,f61])).
% 4.48/1.00  fof(f61,plain,(
% 4.48/1.00    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 4.48/1.00    inference(cnf_transformation,[],[f37])).
% 4.48/1.00  fof(f72,plain,(
% 4.48/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 4.48/1.00    inference(cnf_transformation,[],[f46])).
% 4.48/1.00  fof(f46,plain,(
% 4.48/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 4.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 4.48/1.00  fof(f45,plain,(
% 4.48/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 4.48/1.00    introduced(choice_axiom,[])).
% 4.48/1.00  fof(f44,plain,(
% 4.48/1.00    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 4.48/1.00    inference(rectify,[],[f43])).
% 4.48/1.00  fof(f43,plain,(
% 4.48/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 4.48/1.00    inference(flattening,[],[f42])).
% 4.48/1.00  fof(f42,plain,(
% 4.48/1.00    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 4.48/1.00    inference(nnf_transformation,[],[f28])).
% 4.48/1.00  fof(f3500,plain,(
% 4.48/1.00    r1_tarski(sK2,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(subsumption_resolution,[],[f3460,f83])).
% 4.48/1.00  fof(f83,plain,(
% 4.48/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.48/1.00    inference(equality_resolution,[],[f57])).
% 4.48/1.00  fof(f57,plain,(
% 4.48/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.48/1.00    inference(cnf_transformation,[],[f33])).
% 4.48/1.00  fof(f3460,plain,(
% 4.48/1.00    ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(sK2,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(superposition,[],[f3134,f3420])).
% 4.48/1.00  fof(f3420,plain,(
% 4.48/1.00    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(forward_demodulation,[],[f3369,f48])).
% 4.48/1.00  fof(f48,plain,(
% 4.48/1.00    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 4.48/1.00    inference(cnf_transformation,[],[f31])).
% 4.48/1.00  fof(f31,plain,(
% 4.48/1.00    (sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 4.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f20,f30])).
% 4.48/1.00  fof(f30,plain,(
% 4.48/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4))),
% 4.48/1.00    introduced(choice_axiom,[])).
% 4.48/1.00  fof(f20,plain,(
% 4.48/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.48/1.00    inference(flattening,[],[f19])).
% 4.48/1.00  fof(f19,plain,(
% 4.48/1.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.48/1.00    inference(ennf_transformation,[],[f16])).
% 4.48/1.00  fof(f16,negated_conjecture,(
% 4.48/1.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.48/1.00    inference(negated_conjecture,[],[f15])).
% 4.48/1.00  fof(f15,conjecture,(
% 4.48/1.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 4.48/1.00  fof(f3369,plain,(
% 4.48/1.00    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(superposition,[],[f3137,f53])).
% 4.48/1.00  fof(f53,plain,(
% 4.48/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.48/1.00    inference(cnf_transformation,[],[f17])).
% 4.48/1.00  fof(f17,plain,(
% 4.48/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.48/1.00    inference(rectify,[],[f5])).
% 4.48/1.00  fof(f5,axiom,(
% 4.48/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.48/1.00  fof(f3137,plain,(
% 4.48/1.00    ( ! [X12] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k2_zfmisc_1(sK1,k3_xboole_0(sK2,X12))) )),
% 4.48/1.00    inference(forward_demodulation,[],[f3116,f669])).
% 4.48/1.00  fof(f669,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) )),
% 4.48/1.00    inference(superposition,[],[f82,f53])).
% 4.48/1.00  fof(f82,plain,(
% 4.48/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 4.48/1.00    inference(cnf_transformation,[],[f14])).
% 4.48/1.00  fof(f14,axiom,(
% 4.48/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 4.48/1.00  fof(f3116,plain,(
% 4.48/1.00    ( ! [X12] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X12))) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1368,f3101])).
% 4.48/1.00  fof(f3101,plain,(
% 4.48/1.00    sK1 = k3_xboole_0(sK1,sK3)),
% 4.48/1.00    inference(resolution,[],[f3096,f144])).
% 4.48/1.00  fof(f3096,plain,(
% 4.48/1.00    r1_tarski(sK1,k3_xboole_0(sK1,sK3))),
% 4.48/1.00    inference(resolution,[],[f1364,f83])).
% 4.48/1.00  fof(f1364,plain,(
% 4.48/1.00    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(X5,k3_xboole_0(sK1,sK3))) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1314,f1346])).
% 4.48/1.00  fof(f1346,plain,(
% 4.48/1.00    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(subsumption_resolution,[],[f1344,f248])).
% 4.48/1.00  fof(f248,plain,(
% 4.48/1.00    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(X0,sK4)),k2_zfmisc_1(sK1,sK2))) )),
% 4.48/1.00    inference(superposition,[],[f219,f54])).
% 4.48/1.00  fof(f54,plain,(
% 4.48/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.48/1.00    inference(cnf_transformation,[],[f1])).
% 4.48/1.00  fof(f1,axiom,(
% 4.48/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.48/1.00  fof(f219,plain,(
% 4.48/1.00    ( ! [X4] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X4)),k2_zfmisc_1(sK1,sK2))) )),
% 4.48/1.00    inference(superposition,[],[f142,f48])).
% 4.48/1.00  fof(f142,plain,(
% 4.48/1.00    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,k3_xboole_0(X4,X5)),k2_zfmisc_1(X3,X4))) )),
% 4.48/1.00    inference(resolution,[],[f140,f71])).
% 4.48/1.00  fof(f71,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.48/1.00    inference(cnf_transformation,[],[f26])).
% 4.48/1.00  fof(f26,plain,(
% 4.48/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.48/1.00    inference(ennf_transformation,[],[f12])).
% 4.48/1.00  fof(f12,axiom,(
% 4.48/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 4.48/1.00  fof(f1344,plain,(
% 4.48/1.00    ~r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(sK1,sK2)) | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(resolution,[],[f1338,f58])).
% 4.48/1.00  fof(f1338,plain,(
% 4.48/1.00    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))),
% 4.48/1.00    inference(forward_demodulation,[],[f1334,f48])).
% 4.48/1.00  fof(f1334,plain,(
% 4.48/1.00    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))),
% 4.48/1.00    inference(superposition,[],[f1316,f53])).
% 4.48/1.00  fof(f1316,plain,(
% 4.48/1.00    ( ! [X8] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))) )),
% 4.48/1.00    inference(forward_demodulation,[],[f1315,f730])).
% 4.48/1.00  fof(f730,plain,(
% 4.48/1.00    ( ! [X20] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X20)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X20))) )),
% 4.48/1.00    inference(superposition,[],[f669,f48])).
% 4.48/1.00  fof(f1315,plain,(
% 4.48/1.00    ( ! [X8] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))) )),
% 4.48/1.00    inference(forward_demodulation,[],[f1294,f82])).
% 4.48/1.00  fof(f1294,plain,(
% 4.48/1.00    ( ! [X8] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X8)),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)))) )),
% 4.48/1.00    inference(superposition,[],[f142,f1279])).
% 4.48/1.00  fof(f1279,plain,(
% 4.48/1.00    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))),
% 4.48/1.00    inference(forward_demodulation,[],[f1248,f54])).
% 4.48/1.00  fof(f1248,plain,(
% 4.48/1.00    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))),
% 4.48/1.00    inference(superposition,[],[f730,f674])).
% 4.48/1.00  fof(f674,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 4.48/1.00    inference(superposition,[],[f82,f53])).
% 4.48/1.00  fof(f1314,plain,(
% 4.48/1.00    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) | r1_tarski(X5,k3_xboole_0(sK1,sK3))) )),
% 4.48/1.00    inference(subsumption_resolution,[],[f1291,f50])).
% 4.48/1.00  fof(f50,plain,(
% 4.48/1.00    k1_xboole_0 != sK2),
% 4.48/1.00    inference(cnf_transformation,[],[f31])).
% 4.48/1.00  fof(f1291,plain,(
% 4.48/1.00    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(X5,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4))) | r1_tarski(X5,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK2) )),
% 4.48/1.00    inference(superposition,[],[f80,f1279])).
% 4.48/1.00  fof(f80,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.48/1.00    inference(cnf_transformation,[],[f27])).
% 4.48/1.00  fof(f27,plain,(
% 4.48/1.00    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 4.48/1.00    inference(ennf_transformation,[],[f11])).
% 4.48/1.00  fof(f11,axiom,(
% 4.48/1.00    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 4.48/1.00  fof(f1368,plain,(
% 4.48/1.00    ( ! [X12] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12))) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1320,f1346])).
% 4.48/1.00  fof(f1320,plain,(
% 4.48/1.00    ( ! [X12] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12))) )),
% 4.48/1.00    inference(forward_demodulation,[],[f1319,f730])).
% 4.48/1.00  fof(f1319,plain,(
% 4.48/1.00    ( ! [X12] : (k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12))) )),
% 4.48/1.00    inference(forward_demodulation,[],[f1300,f82])).
% 4.48/1.00  fof(f1300,plain,(
% 4.48/1.00    ( ! [X12] : (k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X12)) = k3_xboole_0(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X12))) )),
% 4.48/1.00    inference(superposition,[],[f669,f1279])).
% 4.48/1.00  fof(f3134,plain,(
% 4.48/1.00    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X6)) | r1_tarski(sK2,X6)) )),
% 4.48/1.00    inference(forward_demodulation,[],[f3133,f3101])).
% 4.48/1.00  fof(f3133,plain,(
% 4.48/1.00    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6)) | r1_tarski(sK2,X6)) )),
% 4.48/1.00    inference(subsumption_resolution,[],[f3110,f49])).
% 4.48/1.00  fof(f49,plain,(
% 4.48/1.00    k1_xboole_0 != sK1),
% 4.48/1.00    inference(cnf_transformation,[],[f31])).
% 4.48/1.00  fof(f3110,plain,(
% 4.48/1.00    ( ! [X6] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6)) | r1_tarski(sK2,X6)) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1352,f3101])).
% 4.48/1.00  fof(f1352,plain,(
% 4.48/1.00    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6)) | r1_tarski(sK2,X6) | k1_xboole_0 = k3_xboole_0(sK1,sK3)) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1292,f1346])).
% 4.48/1.00  fof(f1292,plain,(
% 4.48/1.00    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK2,sK4)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X6)) | r1_tarski(sK2,X6) | k1_xboole_0 = k3_xboole_0(sK1,sK3)) )),
% 4.48/1.00    inference(superposition,[],[f81,f1279])).
% 4.48/1.00  fof(f81,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.48/1.00    inference(cnf_transformation,[],[f27])).
% 4.48/1.00  fof(f148,plain,(
% 4.48/1.00    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 4.48/1.00    inference(superposition,[],[f140,f54])).
% 4.48/1.00  fof(f1720,plain,(
% 4.48/1.00    ~r1_tarski(sK2,sK4) | sK2 = sK4),
% 4.48/1.00    inference(resolution,[],[f1716,f58])).
% 4.48/1.00  fof(f1716,plain,(
% 4.48/1.00    r1_tarski(sK4,sK2)),
% 4.48/1.00    inference(subsumption_resolution,[],[f1710,f49])).
% 4.48/1.00  fof(f1710,plain,(
% 4.48/1.00    r1_tarski(sK4,sK2) | k1_xboole_0 = sK1),
% 4.48/1.00    inference(resolution,[],[f1701,f81])).
% 4.48/1.00  fof(f1701,plain,(
% 4.48/1.00    r1_tarski(k2_zfmisc_1(sK1,sK4),k2_zfmisc_1(sK1,sK2))),
% 4.48/1.00    inference(superposition,[],[f1544,f48])).
% 4.48/1.00  fof(f1544,plain,(
% 4.48/1.00    ( ! [X2] : (r1_tarski(k2_zfmisc_1(sK1,X2),k2_zfmisc_1(sK3,X2))) )),
% 4.48/1.00    inference(resolution,[],[f1541,f70])).
% 4.48/1.00  fof(f70,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.48/1.00    inference(cnf_transformation,[],[f26])).
% 4.48/1.00  fof(f1541,plain,(
% 4.48/1.00    r1_tarski(sK1,sK3)),
% 4.48/1.00    inference(subsumption_resolution,[],[f1535,f50])).
% 4.48/1.00  fof(f1535,plain,(
% 4.48/1.00    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 4.48/1.00    inference(resolution,[],[f1484,f80])).
% 4.48/1.00  fof(f1484,plain,(
% 4.48/1.00    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))),
% 4.48/1.00    inference(superposition,[],[f179,f1347])).
% 4.48/1.00  fof(f1347,plain,(
% 4.48/1.00    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2)),
% 4.48/1.00    inference(backward_demodulation,[],[f1279,f1346])).
% 4.48/1.00  fof(f179,plain,(
% 4.48/1.00    ( ! [X6,X8,X7] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X6,X7),X8),k2_zfmisc_1(X7,X8))) )),
% 4.48/1.00    inference(resolution,[],[f148,f70])).
% 4.48/1.00  fof(f51,plain,(
% 4.48/1.00    sK2 != sK4 | sK1 != sK3),
% 4.48/1.00    inference(cnf_transformation,[],[f31])).
% 4.48/1.00  fof(f1545,plain,(
% 4.48/1.00    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 4.48/1.00    inference(resolution,[],[f1541,f58])).
% 4.48/1.00  fof(f4697,plain,(
% 4.48/1.00    r1_tarski(sK3,sK1)),
% 4.48/1.00    inference(resolution,[],[f3766,f83])).
% 4.48/1.00  fof(f3766,plain,(
% 4.48/1.00    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(X4,sK2)) | r1_tarski(sK3,X4)) )),
% 4.48/1.00    inference(backward_demodulation,[],[f1646,f3598])).
% 4.48/1.00  fof(f3598,plain,(
% 4.48/1.00    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK2)),
% 4.48/1.00    inference(backward_demodulation,[],[f1346,f3589])).
% 4.48/1.00  fof(f1646,plain,(
% 4.48/1.00    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(X4,sK2)) | r1_tarski(sK3,X4)) )),
% 4.48/1.00    inference(forward_demodulation,[],[f1578,f1565])).
% 4.48/1.00  fof(f1565,plain,(
% 4.48/1.00    k2_zfmisc_1(sK3,sK2) = k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2))),
% 4.48/1.00    inference(backward_demodulation,[],[f568,f1546])).
% 4.48/1.00  fof(f1546,plain,(
% 4.48/1.00    sK3 = k2_xboole_0(sK1,sK3)),
% 4.48/1.00    inference(resolution,[],[f1541,f55])).
% 4.48/1.00  fof(f55,plain,(
% 4.48/1.00    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.48/1.00    inference(cnf_transformation,[],[f21])).
% 4.48/1.00  fof(f21,plain,(
% 4.48/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.48/1.00    inference(ennf_transformation,[],[f8])).
% 4.48/1.00  fof(f8,axiom,(
% 4.48/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.48/1.00  fof(f568,plain,(
% 4.48/1.00    k2_zfmisc_1(k2_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2))),
% 4.48/1.00    inference(superposition,[],[f376,f68])).
% 4.48/1.00  fof(f68,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.48/1.00    inference(cnf_transformation,[],[f13])).
% 4.48/1.00  fof(f13,axiom,(
% 4.48/1.00    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 4.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 4.48/1.00  fof(f376,plain,(
% 4.48/1.00    ( ! [X7] : (k2_zfmisc_1(sK3,k2_xboole_0(sK4,X7)) = k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X7))) )),
% 4.48/1.00    inference(superposition,[],[f69,f48])).
% 4.48/1.00  fof(f69,plain,(
% 4.48/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.48/1.00    inference(cnf_transformation,[],[f13])).
% 4.48/1.00  fof(f1578,plain,(
% 4.48/1.00    ( ! [X4] : (r1_tarski(sK3,X4) | ~r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2))) )),
% 4.48/1.00    inference(backward_demodulation,[],[f618,f1546])).
% 4.48/1.00  fof(f618,plain,(
% 4.48/1.00    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2)) | r1_tarski(k2_xboole_0(sK1,sK3),X4)) )),
% 4.48/1.00    inference(subsumption_resolution,[],[f607,f50])).
% 4.48/1.00  fof(f607,plain,(
% 4.48/1.00    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK3,k2_xboole_0(sK4,sK2)),k2_zfmisc_1(X4,sK2)) | r1_tarski(k2_xboole_0(sK1,sK3),X4) | k1_xboole_0 = sK2) )),
% 4.48/1.00    inference(superposition,[],[f80,f568])).
% 4.48/1.00  % SZS output end Proof for theBenchmark
% 4.48/1.00  % (28926)------------------------------
% 4.48/1.00  % (28926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/1.00  % (28926)Termination reason: Refutation
% 4.48/1.00  
% 4.48/1.00  % (28926)Memory used [KB]: 9850
% 4.48/1.00  % (28926)Time elapsed: 0.562 s
% 4.48/1.00  % (28926)------------------------------
% 4.48/1.00  % (28926)------------------------------
% 4.48/1.00  % (28918)Success in time 0.636 s
%------------------------------------------------------------------------------
