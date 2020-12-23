%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 383 expanded)
%              Number of leaves         :   11 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  235 (1599 expanded)
%              Number of equality atoms :   99 ( 620 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(subsumption_resolution,[],[f263,f143])).

fof(f143,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f58,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f136,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f6,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f136,plain,(
    ! [X3] : sP0(k1_xboole_0,X3,k1_xboole_0) ),
    inference(resolution,[],[f122,f63])).

fof(f63,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(superposition,[],[f57,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f57,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f122,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(k1_xboole_0,X4,X5),X5)
      | sP0(k1_xboole_0,X4,X5) ) ),
    inference(resolution,[],[f44,f63])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
              & r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
                & r2_hidden(sK7(X0,X1,X8),X0)
                & r2_hidden(sK6(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK3(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK3(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(sK4(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8
        & r2_hidden(sK7(X0,X1,X8),X0)
        & r2_hidden(sK6(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f58,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( k1_xboole_0 != sK2
        & k1_xboole_0 != sK1 )
      | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK2
          & k1_xboole_0 != sK1 )
        | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ) ) ),
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f263,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f262,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,(
    ! [X3] : sP0(X3,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,k1_xboole_0,X5),X5)
      | sP0(X4,k1_xboole_0,X5) ) ),
    inference(resolution,[],[f43,f63])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f262,plain,(
    ! [X2] : sK2 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f258,f48])).

fof(f258,plain,(
    ! [X3] : sP0(X3,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f257,f104])).

fof(f104,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f59,f103])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f257,plain,(
    ! [X3] :
      ( k1_xboole_0 = sK1
      | sP0(X3,k1_xboole_0,sK2) ) ),
    inference(forward_demodulation,[],[f254,f103])).

fof(f254,plain,(
    ! [X4,X3] :
      ( sP0(X3,k1_xboole_0,sK2)
      | sK1 = k2_zfmisc_1(k1_xboole_0,X4) ) ),
    inference(resolution,[],[f243,f48])).

fof(f243,plain,(
    ! [X6,X7] :
      ( sP0(X6,k1_xboole_0,sK1)
      | sP0(X7,k1_xboole_0,sK2) ) ),
    inference(resolution,[],[f240,f83])).

fof(f240,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,sK2)
      | sP0(X3,k1_xboole_0,sK1) ) ),
    inference(subsumption_resolution,[],[f238,f63])).

fof(f238,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(sK3(X3,k1_xboole_0,sK1),X4),k1_xboole_0)
      | ~ r2_hidden(X4,sK2)
      | sP0(X3,k1_xboole_0,sK1) ) ),
    inference(superposition,[],[f99,f145])).

fof(f145,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f106,f143])).

fof(f106,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f31,f104])).

fof(f31,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(k4_tarski(sK3(X9,k1_xboole_0,X10),X11),k2_zfmisc_1(X10,X12))
      | ~ r2_hidden(X11,X12)
      | sP0(X9,k1_xboole_0,X10) ) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (6387)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.47  % (6387)Refutation not found, incomplete strategy% (6387)------------------------------
% 0.20/0.47  % (6387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6387)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6387)Memory used [KB]: 1663
% 0.20/0.47  % (6387)Time elapsed: 0.085 s
% 0.20/0.47  % (6387)------------------------------
% 0.20/0.47  % (6387)------------------------------
% 0.20/0.51  % (6403)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (6395)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (6410)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (6395)Refutation not found, incomplete strategy% (6395)------------------------------
% 0.20/0.53  % (6395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6395)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6395)Memory used [KB]: 10618
% 0.20/0.53  % (6395)Time elapsed: 0.125 s
% 0.20/0.53  % (6395)------------------------------
% 0.20/0.53  % (6395)------------------------------
% 0.20/0.54  % (6389)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (6393)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (6389)Refutation not found, incomplete strategy% (6389)------------------------------
% 0.20/0.54  % (6389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6394)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (6413)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (6389)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6389)Memory used [KB]: 10618
% 0.20/0.55  % (6389)Time elapsed: 0.125 s
% 0.20/0.55  % (6389)------------------------------
% 0.20/0.55  % (6389)------------------------------
% 0.20/0.56  % (6405)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.56  % (6397)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.56  % (6412)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.57  % (6411)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.57  % (6397)Refutation not found, incomplete strategy% (6397)------------------------------
% 1.47/0.57  % (6397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (6391)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.57  % (6412)Refutation not found, incomplete strategy% (6412)------------------------------
% 1.47/0.57  % (6412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (6412)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (6412)Memory used [KB]: 6268
% 1.47/0.57  % (6412)Time elapsed: 0.100 s
% 1.47/0.57  % (6412)------------------------------
% 1.47/0.57  % (6412)------------------------------
% 1.47/0.57  % (6397)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (6397)Memory used [KB]: 10618
% 1.47/0.57  % (6391)Refutation not found, incomplete strategy% (6391)------------------------------
% 1.47/0.57  % (6391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (6391)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (6391)Memory used [KB]: 6268
% 1.47/0.57  % (6391)Time elapsed: 0.144 s
% 1.47/0.57  % (6391)------------------------------
% 1.47/0.57  % (6391)------------------------------
% 1.47/0.57  % (6397)Time elapsed: 0.142 s
% 1.47/0.57  % (6397)------------------------------
% 1.47/0.57  % (6397)------------------------------
% 1.47/0.57  % (6392)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.47/0.57  % (6398)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.57  % (6398)Refutation not found, incomplete strategy% (6398)------------------------------
% 1.47/0.57  % (6398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (6398)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (6398)Memory used [KB]: 10618
% 1.47/0.57  % (6398)Time elapsed: 0.154 s
% 1.47/0.57  % (6398)------------------------------
% 1.47/0.57  % (6398)------------------------------
% 1.47/0.58  % (6401)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.58  % (6402)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.74/0.59  % (6390)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.74/0.59  % (6409)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.74/0.59  % (6414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.74/0.60  % (6407)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.60  % (6394)Refutation found. Thanks to Tanya!
% 1.74/0.60  % SZS status Theorem for theBenchmark
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f264,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(subsumption_resolution,[],[f263,f143])).
% 1.74/0.60  fof(f143,plain,(
% 1.74/0.60    k1_xboole_0 != sK2),
% 1.74/0.60    inference(subsumption_resolution,[],[f58,f142])).
% 1.74/0.60  fof(f142,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.74/0.60    inference(resolution,[],[f136,f48])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.74/0.60    inference(cnf_transformation,[],[f26])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 1.74/0.60    inference(nnf_transformation,[],[f15])).
% 1.74/0.60  fof(f15,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.74/0.60    inference(definition_folding,[],[f6,f14])).
% 1.74/0.60  fof(f14,plain,(
% 1.74/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.74/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.74/0.60  fof(f6,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.74/0.60  fof(f136,plain,(
% 1.74/0.60    ( ! [X3] : (sP0(k1_xboole_0,X3,k1_xboole_0)) )),
% 1.74/0.60    inference(resolution,[],[f122,f63])).
% 1.74/0.60  fof(f63,plain,(
% 1.74/0.60    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.74/0.60    inference(superposition,[],[f57,f60])).
% 1.74/0.60  fof(f60,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.74/0.60    inference(resolution,[],[f37,f35])).
% 1.74/0.60  fof(f35,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.74/0.60  fof(f37,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f13])).
% 1.74/0.60  fof(f13,plain,(
% 1.74/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f11])).
% 1.74/0.60  fof(f11,plain,(
% 1.74/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.74/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.74/0.60  fof(f57,plain,(
% 1.74/0.60    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.74/0.60    inference(equality_resolution,[],[f50])).
% 1.74/0.60  fof(f50,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.74/0.60    inference(flattening,[],[f27])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.74/0.60    inference(nnf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.74/0.60  fof(f122,plain,(
% 1.74/0.60    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4,X5),X5) | sP0(k1_xboole_0,X4,X5)) )),
% 1.74/0.60    inference(resolution,[],[f44,f63])).
% 1.74/0.60  fof(f44,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f24,f23,f22])).
% 1.74/0.60  fof(f22,plain,(
% 1.74/0.60    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK3(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK3(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK3(X0,X1,X2) = k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f24,plain,(
% 1.74/0.60    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK6(X0,X1,X8),sK7(X0,X1,X8)) = X8 & r2_hidden(sK7(X0,X1,X8),X0) & r2_hidden(sK6(X0,X1,X8),X1)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f21,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 1.74/0.60    inference(rectify,[],[f20])).
% 1.74/0.60  fof(f20,plain,(
% 1.74/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.74/0.60    inference(nnf_transformation,[],[f14])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)),
% 1.74/0.60    inference(inner_rewriting,[],[f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,plain,(
% 1.74/0.60    ((k1_xboole_0 != sK2 & k1_xboole_0 != sK1) | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)) & (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK2))),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f18])).
% 1.74/0.60  fof(f18,plain,(
% 1.74/0.60    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK2 & k1_xboole_0 != sK1) | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)) & (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f17,plain,(
% 1.74/0.60    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.74/0.60    inference(flattening,[],[f16])).
% 1.74/0.60  fof(f16,plain,(
% 1.74/0.60    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.74/0.60    inference(nnf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,plain,(
% 1.74/0.60    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f10])).
% 1.74/0.60  fof(f10,negated_conjecture,(
% 1.74/0.60    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.74/0.60    inference(negated_conjecture,[],[f9])).
% 1.74/0.60  fof(f9,conjecture,(
% 1.74/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.74/0.60  fof(f263,plain,(
% 1.74/0.60    k1_xboole_0 = sK2),
% 1.74/0.60    inference(forward_demodulation,[],[f262,f103])).
% 1.74/0.60  fof(f103,plain,(
% 1.74/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.74/0.60    inference(resolution,[],[f97,f48])).
% 1.74/0.60  fof(f97,plain,(
% 1.74/0.60    ( ! [X3] : (sP0(X3,k1_xboole_0,k1_xboole_0)) )),
% 1.74/0.60    inference(resolution,[],[f83,f63])).
% 1.74/0.60  fof(f83,plain,(
% 1.74/0.60    ( ! [X4,X5] : (r2_hidden(sK3(X4,k1_xboole_0,X5),X5) | sP0(X4,k1_xboole_0,X5)) )),
% 1.74/0.60    inference(resolution,[],[f43,f63])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f25])).
% 1.74/0.60  fof(f262,plain,(
% 1.74/0.60    ( ! [X2] : (sK2 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 1.74/0.60    inference(resolution,[],[f258,f48])).
% 1.74/0.60  fof(f258,plain,(
% 1.74/0.60    ( ! [X3] : (sP0(X3,k1_xboole_0,sK2)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f257,f104])).
% 1.74/0.60  fof(f104,plain,(
% 1.74/0.60    k1_xboole_0 != sK1),
% 1.74/0.60    inference(subsumption_resolution,[],[f59,f103])).
% 1.74/0.60  fof(f59,plain,(
% 1.74/0.60    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 1.74/0.60    inference(inner_rewriting,[],[f32])).
% 1.74/0.60  fof(f32,plain,(
% 1.74/0.60    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f257,plain,(
% 1.74/0.60    ( ! [X3] : (k1_xboole_0 = sK1 | sP0(X3,k1_xboole_0,sK2)) )),
% 1.74/0.60    inference(forward_demodulation,[],[f254,f103])).
% 1.74/0.60  fof(f254,plain,(
% 1.74/0.60    ( ! [X4,X3] : (sP0(X3,k1_xboole_0,sK2) | sK1 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 1.74/0.60    inference(resolution,[],[f243,f48])).
% 1.74/0.60  fof(f243,plain,(
% 1.74/0.60    ( ! [X6,X7] : (sP0(X6,k1_xboole_0,sK1) | sP0(X7,k1_xboole_0,sK2)) )),
% 1.74/0.60    inference(resolution,[],[f240,f83])).
% 1.74/0.60  fof(f240,plain,(
% 1.74/0.60    ( ! [X4,X3] : (~r2_hidden(X4,sK2) | sP0(X3,k1_xboole_0,sK1)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f238,f63])).
% 1.74/0.60  fof(f238,plain,(
% 1.74/0.60    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK3(X3,k1_xboole_0,sK1),X4),k1_xboole_0) | ~r2_hidden(X4,sK2) | sP0(X3,k1_xboole_0,sK1)) )),
% 1.74/0.60    inference(superposition,[],[f99,f145])).
% 1.74/0.60  fof(f145,plain,(
% 1.74/0.60    k1_xboole_0 = k2_zfmisc_1(sK1,sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f106,f143])).
% 1.74/0.60  fof(f106,plain,(
% 1.74/0.60    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | k1_xboole_0 = sK2),
% 1.74/0.60    inference(subsumption_resolution,[],[f31,f104])).
% 1.74/0.60  fof(f31,plain,(
% 1.74/0.60    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.74/0.60    inference(cnf_transformation,[],[f19])).
% 1.74/0.60  fof(f99,plain,(
% 1.74/0.60    ( ! [X12,X10,X11,X9] : (r2_hidden(k4_tarski(sK3(X9,k1_xboole_0,X10),X11),k2_zfmisc_1(X10,X12)) | ~r2_hidden(X11,X12) | sP0(X9,k1_xboole_0,X10)) )),
% 1.74/0.60    inference(resolution,[],[f83,f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f30])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.74/0.60    inference(flattening,[],[f29])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.74/0.60    inference(nnf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (6394)------------------------------
% 1.74/0.60  % (6394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (6394)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (6394)Memory used [KB]: 6652
% 1.74/0.60  % (6394)Time elapsed: 0.177 s
% 1.74/0.60  % (6394)------------------------------
% 1.74/0.60  % (6394)------------------------------
% 1.74/0.60  % (6404)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.74/0.60  % (6386)Success in time 0.236 s
%------------------------------------------------------------------------------
