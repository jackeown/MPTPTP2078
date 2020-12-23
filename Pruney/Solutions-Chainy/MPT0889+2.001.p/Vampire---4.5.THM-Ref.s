%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:05 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 244 expanded)
%              Number of leaves         :   15 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  303 (1028 expanded)
%              Number of equality atoms :   51 ( 213 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1219,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f1187,f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f11,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f1187,plain,(
    ~ sP0(sK6(sK3),sK3) ),
    inference(resolution,[],[f1178,f69])).

fof(f69,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f17,f16])).

fof(f16,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1178,plain,(
    ! [X0] :
      ( ~ sP2(sK5,sK3,X0)
      | ~ sP0(sK6(sK3),sK3) ) ),
    inference(subsumption_resolution,[],[f1177,f499])).

fof(f499,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP0(X3,X1)
      | ~ sP1(X3,X4,X2) ) ),
    inference(superposition,[],[f474,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f474,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X2,k2_zfmisc_1(X3,X1))
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ sP1(X0,X2,k2_zfmisc_1(X3,X1))
      | ~ sP1(X0,X2,k2_zfmisc_1(X3,X1)) ) ),
    inference(resolution,[],[f153,f83])).

fof(f83,plain,(
    ! [X6,X8,X7,X5] :
      ( sP1(sK9(X5,X6,k2_zfmisc_1(X7,X8)),X8,X7)
      | ~ sP1(X5,X6,k2_zfmisc_1(X7,X8)) ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0
          & r2_hidden(sK10(X0,X1,X2),X1)
          & r2_hidden(sK9(X0,X1,X2),X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0
        & r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f53,f69])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(sK8(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP1(sK8(X0,X1,X2),X1,X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(sK8(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP1(sK8(X0,X1,X2),X1,X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X3,X1,X0) )
            & ( sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f153,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(sK9(X0,X1,X2),X3,X4)
      | ~ sP0(X0,X3)
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f145,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(k4_tarski(X0,X1),X2)
      | ~ sP1(X0,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(k4_tarski(X0,X1),X2)
      | ~ sP1(X0,X2,X3)
      | ~ sP1(X0,X2,X3) ) ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ r2_hidden(sK10(X10,X11,X12),X14)
      | ~ sP0(k4_tarski(X10,X13),X14)
      | ~ sP1(X10,X11,X12) ) ),
    inference(superposition,[],[f66,f59])).

fof(f66,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X0
          | ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f1177,plain,(
    ! [X0] :
      ( ~ sP2(sK5,sK3,X0)
      | ~ sP0(sK6(sK3),sK3)
      | sP1(sK6(sK3),sK4,X0) ) ),
    inference(subsumption_resolution,[],[f1167,f39])).

fof(f1167,plain,(
    ! [X0] :
      ( ~ sP2(sK5,sK3,X0)
      | ~ sP0(sK6(sK3),sK3)
      | k1_xboole_0 = sK3
      | sP1(sK6(sK3),sK4,X0) ) ),
    inference(resolution,[],[f860,f97])).

fof(f97,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | k1_xboole_0 = X3
      | sP1(sK6(X3),X5,X4) ) ),
    inference(resolution,[],[f72,f80])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0),X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f860,plain,(
    ! [X3] :
      ( r1_tarski(sK3,k2_zfmisc_1(X3,sK4))
      | ~ sP2(sK5,sK3,X3)
      | ~ sP0(sK6(sK3),sK3) ) ),
    inference(resolution,[],[f304,f462])).

fof(f462,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X2,k2_zfmisc_1(X1,X3))
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ sP1(X0,X2,k2_zfmisc_1(X1,X3))
      | ~ sP1(X0,X2,k2_zfmisc_1(X1,X3)) ) ),
    inference(resolution,[],[f138,f83])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(sK9(X0,X1,X2),X4,X3)
      | ~ sP0(X0,X3)
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f137,f59])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(k4_tarski(X0,X1),X2)
      | ~ sP1(X0,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(k4_tarski(X0,X1),X2)
      | ~ sP1(X0,X3,X2)
      | ~ sP1(X0,X3,X2) ) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(sK9(X5,X6,X7),X9)
      | ~ sP0(k4_tarski(X5,X8),X9)
      | ~ sP1(X5,X6,X7) ) ),
    inference(superposition,[],[f67,f59])).

fof(f67,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP0(k4_tarski(k4_tarski(X2,X3),X4),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X2,X3),X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_mcart_1(X2,X3,X4) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f304,plain,(
    ! [X0] :
      ( sP1(sK6(sK3),sK5,k2_zfmisc_1(sK3,sK4))
      | ~ sP2(sK5,sK3,X0)
      | r1_tarski(sK3,k2_zfmisc_1(X0,sK4)) ) ),
    inference(subsumption_resolution,[],[f300,f39])).

fof(f300,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK4))
      | ~ sP2(sK5,sK3,X0)
      | k1_xboole_0 = sK3
      | sP1(sK6(sK3),sK5,k2_zfmisc_1(sK3,sK4)) ) ),
    inference(resolution,[],[f157,f97])).

fof(f157,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
      | r1_tarski(sK3,k2_zfmisc_1(X0,sK4))
      | ~ sP2(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f154,f39])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(X0,sK4))
      | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
      | ~ sP2(sK5,sK3,X0)
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK3))
      | r1_tarski(sK3,k2_zfmisc_1(X0,sK4))
      | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
      | ~ sP2(sK5,sK3,X0) ) ),
    inference(superposition,[],[f63,f62])).

fof(f63,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK5,sK3),sK4))
    | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK3))
    | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f38,f52,f52,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f38,plain,
    ( r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4))
    | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3))
    | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK3
    & ( r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4))
      | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3))
      | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) )
   => ( k1_xboole_0 != sK3
      & ( r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4))
        | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3))
        | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
            & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
            & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f39,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:23:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (17811)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (17824)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (17801)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (17820)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (17813)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (17804)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (17822)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (17822)Refutation not found, incomplete strategy% (17822)------------------------------
% 0.20/0.52  % (17822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17806)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (17822)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (17822)Memory used [KB]: 10746
% 0.20/0.52  % (17822)Time elapsed: 0.108 s
% 0.20/0.52  % (17822)------------------------------
% 0.20/0.52  % (17822)------------------------------
% 0.20/0.52  % (17810)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (17809)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (17807)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (17823)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (17814)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (17805)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (17820)Refutation not found, incomplete strategy% (17820)------------------------------
% 0.20/0.54  % (17820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17820)Memory used [KB]: 10746
% 0.20/0.54  % (17820)Time elapsed: 0.132 s
% 0.20/0.54  % (17820)------------------------------
% 0.20/0.54  % (17820)------------------------------
% 0.20/0.54  % (17802)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (17802)Refutation not found, incomplete strategy% (17802)------------------------------
% 0.20/0.54  % (17802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17802)Memory used [KB]: 10746
% 0.20/0.54  % (17802)Time elapsed: 0.129 s
% 0.20/0.54  % (17802)------------------------------
% 0.20/0.54  % (17802)------------------------------
% 0.20/0.54  % (17829)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (17803)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (17825)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (17827)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (17818)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (17815)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (17821)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (17817)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (17828)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (17817)Refutation not found, incomplete strategy% (17817)------------------------------
% 0.20/0.56  % (17817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (17817)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (17817)Memory used [KB]: 10746
% 0.20/0.56  % (17817)Time elapsed: 0.141 s
% 0.20/0.56  % (17817)------------------------------
% 0.20/0.56  % (17817)------------------------------
% 0.20/0.56  % (17812)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (17816)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (17819)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  % (17800)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.58  % (17808)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.58  % (17826)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.60  % (17808)Refutation not found, incomplete strategy% (17808)------------------------------
% 0.20/0.60  % (17808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (17808)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (17808)Memory used [KB]: 10618
% 0.20/0.60  % (17808)Time elapsed: 0.158 s
% 0.20/0.60  % (17808)------------------------------
% 0.20/0.60  % (17808)------------------------------
% 2.21/0.68  % (17829)Refutation found. Thanks to Tanya!
% 2.21/0.68  % SZS status Theorem for theBenchmark
% 2.21/0.68  % SZS output start Proof for theBenchmark
% 2.21/0.68  fof(f1219,plain,(
% 2.21/0.68    $false),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f39,f1187,f43])).
% 2.21/0.68  fof(f43,plain,(
% 2.21/0.68    ( ! [X0] : (sP0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f24])).
% 2.21/0.68  fof(f24,plain,(
% 2.21/0.68    ! [X0] : ((sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f23])).
% 2.21/0.68  fof(f23,plain,(
% 2.21/0.68    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f15,plain,(
% 2.21/0.68    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.21/0.68    inference(definition_folding,[],[f11,f14])).
% 2.21/0.68  fof(f14,plain,(
% 2.21/0.68    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 2.21/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.21/0.68  fof(f11,plain,(
% 2.21/0.68    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.21/0.68    inference(ennf_transformation,[],[f6])).
% 2.21/0.68  fof(f6,axiom,(
% 2.21/0.68    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 2.21/0.68  fof(f1187,plain,(
% 2.21/0.68    ~sP0(sK6(sK3),sK3)),
% 2.21/0.68    inference(resolution,[],[f1178,f69])).
% 2.21/0.68  fof(f69,plain,(
% 2.21/0.68    ( ! [X0,X1] : (sP2(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.21/0.68    inference(equality_resolution,[],[f61])).
% 2.21/0.68  fof(f61,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.21/0.68    inference(cnf_transformation,[],[f37])).
% 2.21/0.68  fof(f37,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 2.21/0.68    inference(nnf_transformation,[],[f18])).
% 2.21/0.68  fof(f18,plain,(
% 2.21/0.68    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 2.21/0.68    inference(definition_folding,[],[f2,f17,f16])).
% 2.21/0.68  fof(f16,plain,(
% 2.21/0.68    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 2.21/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.21/0.68  fof(f17,plain,(
% 2.21/0.68    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 2.21/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.21/0.68  fof(f2,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.21/0.68  fof(f1178,plain,(
% 2.21/0.68    ( ! [X0] : (~sP2(sK5,sK3,X0) | ~sP0(sK6(sK3),sK3)) )),
% 2.21/0.68    inference(subsumption_resolution,[],[f1177,f499])).
% 2.21/0.68  fof(f499,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (~sP2(X0,X1,X2) | ~sP0(X3,X1) | ~sP1(X3,X4,X2)) )),
% 2.21/0.68    inference(superposition,[],[f474,f62])).
% 2.21/0.68  fof(f62,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f37])).
% 2.21/0.68  fof(f474,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP1(X0,X2,k2_zfmisc_1(X3,X1)) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(duplicate_literal_removal,[],[f469])).
% 2.21/0.68  fof(f469,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1) | ~sP1(X0,X2,k2_zfmisc_1(X3,X1)) | ~sP1(X0,X2,k2_zfmisc_1(X3,X1))) )),
% 2.21/0.68    inference(resolution,[],[f153,f83])).
% 2.21/0.68  fof(f83,plain,(
% 2.21/0.68    ( ! [X6,X8,X7,X5] : (sP1(sK9(X5,X6,k2_zfmisc_1(X7,X8)),X8,X7) | ~sP1(X5,X6,k2_zfmisc_1(X7,X8))) )),
% 2.21/0.68    inference(resolution,[],[f80,f57])).
% 2.21/0.68  fof(f57,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X2) | ~sP1(X0,X1,X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f36])).
% 2.21/0.68  fof(f36,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0 & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2)) | ~sP1(X0,X1,X2)))),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f34,f35])).
% 2.21/0.68  fof(f35,plain,(
% 2.21/0.68    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0 & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2)))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f34,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP1(X0,X1,X2)))),
% 2.21/0.68    inference(rectify,[],[f33])).
% 2.21/0.68  fof(f33,plain,(
% 2.21/0.68    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP1(X3,X1,X0)))),
% 2.21/0.68    inference(nnf_transformation,[],[f16])).
% 2.21/0.68  fof(f80,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP1(X0,X2,X1)) )),
% 2.21/0.68    inference(resolution,[],[f53,f69])).
% 2.21/0.68  fof(f53,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X4,X1,X0)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f32])).
% 2.21/0.68  fof(f32,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK8(X0,X1,X2),X1,X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(sK8(X0,X1,X2),X1,X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).
% 2.21/0.68  fof(f31,plain,(
% 2.21/0.68    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK8(X0,X1,X2),X1,X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(sK8(X0,X1,X2),X1,X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f30,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.21/0.68    inference(rectify,[],[f29])).
% 2.21/0.68  fof(f29,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 2.21/0.68    inference(nnf_transformation,[],[f17])).
% 2.21/0.68  fof(f153,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (~sP1(sK9(X0,X1,X2),X3,X4) | ~sP0(X0,X3) | ~sP1(X0,X1,X2)) )),
% 2.21/0.68    inference(superposition,[],[f145,f59])).
% 2.21/0.68  fof(f59,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) = X0 | ~sP1(X0,X1,X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f36])).
% 2.21/0.68  fof(f145,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(k4_tarski(X0,X1),X2) | ~sP1(X0,X2,X3)) )),
% 2.21/0.68    inference(duplicate_literal_removal,[],[f139])).
% 2.21/0.68  fof(f139,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(k4_tarski(X0,X1),X2) | ~sP1(X0,X2,X3) | ~sP1(X0,X2,X3)) )),
% 2.21/0.68    inference(resolution,[],[f93,f58])).
% 2.21/0.68  fof(f58,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X1) | ~sP1(X0,X1,X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f36])).
% 2.21/0.68  fof(f93,plain,(
% 2.21/0.68    ( ! [X14,X12,X10,X13,X11] : (~r2_hidden(sK10(X10,X11,X12),X14) | ~sP0(k4_tarski(X10,X13),X14) | ~sP1(X10,X11,X12)) )),
% 2.21/0.68    inference(superposition,[],[f66,f59])).
% 2.21/0.68  fof(f66,plain,(
% 2.21/0.68    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X3,X1)) )),
% 2.21/0.68    inference(equality_resolution,[],[f64])).
% 2.21/0.68  fof(f64,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(definition_unfolding,[],[f41,f51])).
% 2.21/0.68  fof(f51,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f4])).
% 2.21/0.68  fof(f4,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.21/0.68  fof(f41,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f22])).
% 2.21/0.68  fof(f22,plain,(
% 2.21/0.68    ! [X0,X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X0 | (~r2_hidden(X3,X1) & ~r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 2.21/0.68    inference(rectify,[],[f21])).
% 2.21/0.68  fof(f21,plain,(
% 2.21/0.68    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 2.21/0.68    inference(nnf_transformation,[],[f14])).
% 2.21/0.68  fof(f1177,plain,(
% 2.21/0.68    ( ! [X0] : (~sP2(sK5,sK3,X0) | ~sP0(sK6(sK3),sK3) | sP1(sK6(sK3),sK4,X0)) )),
% 2.21/0.68    inference(subsumption_resolution,[],[f1167,f39])).
% 2.21/0.68  fof(f1167,plain,(
% 2.21/0.68    ( ! [X0] : (~sP2(sK5,sK3,X0) | ~sP0(sK6(sK3),sK3) | k1_xboole_0 = sK3 | sP1(sK6(sK3),sK4,X0)) )),
% 2.21/0.68    inference(resolution,[],[f860,f97])).
% 2.21/0.68  fof(f97,plain,(
% 2.21/0.68    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | k1_xboole_0 = X3 | sP1(sK6(X3),X5,X4)) )),
% 2.21/0.68    inference(resolution,[],[f72,f80])).
% 2.21/0.68  fof(f72,plain,(
% 2.21/0.68    ( ! [X0,X1] : (r2_hidden(sK6(X0),X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 2.21/0.68    inference(resolution,[],[f48,f42])).
% 2.21/0.68  fof(f42,plain,(
% 2.21/0.68    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f24])).
% 2.21/0.68  fof(f48,plain,(
% 2.21/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f28])).
% 2.21/0.68  fof(f28,plain,(
% 2.21/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).
% 2.21/0.68  fof(f27,plain,(
% 2.21/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f26,plain,(
% 2.21/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.68    inference(rectify,[],[f25])).
% 2.21/0.68  fof(f25,plain,(
% 2.21/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.68    inference(nnf_transformation,[],[f13])).
% 2.21/0.68  fof(f13,plain,(
% 2.21/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.21/0.68    inference(ennf_transformation,[],[f1])).
% 2.21/0.68  fof(f1,axiom,(
% 2.21/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.21/0.68  fof(f860,plain,(
% 2.21/0.68    ( ! [X3] : (r1_tarski(sK3,k2_zfmisc_1(X3,sK4)) | ~sP2(sK5,sK3,X3) | ~sP0(sK6(sK3),sK3)) )),
% 2.21/0.68    inference(resolution,[],[f304,f462])).
% 2.21/0.68  fof(f462,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP1(X0,X2,k2_zfmisc_1(X1,X3)) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(duplicate_literal_removal,[],[f457])).
% 2.21/0.68  fof(f457,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1) | ~sP1(X0,X2,k2_zfmisc_1(X1,X3)) | ~sP1(X0,X2,k2_zfmisc_1(X1,X3))) )),
% 2.21/0.68    inference(resolution,[],[f138,f83])).
% 2.21/0.68  fof(f138,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (~sP1(sK9(X0,X1,X2),X4,X3) | ~sP0(X0,X3) | ~sP1(X0,X1,X2)) )),
% 2.21/0.68    inference(superposition,[],[f137,f59])).
% 2.21/0.68  fof(f137,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(k4_tarski(X0,X1),X2) | ~sP1(X0,X3,X2)) )),
% 2.21/0.68    inference(duplicate_literal_removal,[],[f131])).
% 2.21/0.68  fof(f131,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~sP0(k4_tarski(X0,X1),X2) | ~sP1(X0,X3,X2) | ~sP1(X0,X3,X2)) )),
% 2.21/0.68    inference(resolution,[],[f92,f57])).
% 2.21/0.68  fof(f92,plain,(
% 2.21/0.68    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(sK9(X5,X6,X7),X9) | ~sP0(k4_tarski(X5,X8),X9) | ~sP1(X5,X6,X7)) )),
% 2.21/0.68    inference(superposition,[],[f67,f59])).
% 2.21/0.68  fof(f67,plain,(
% 2.21/0.68    ( ! [X4,X2,X3,X1] : (~sP0(k4_tarski(k4_tarski(X2,X3),X4),X1) | ~r2_hidden(X2,X1)) )),
% 2.21/0.68    inference(equality_resolution,[],[f65])).
% 2.21/0.68  fof(f65,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(X2,X3),X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(definition_unfolding,[],[f40,f51])).
% 2.21/0.68  fof(f40,plain,(
% 2.21/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_mcart_1(X2,X3,X4) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f22])).
% 2.21/0.68  fof(f304,plain,(
% 2.21/0.68    ( ! [X0] : (sP1(sK6(sK3),sK5,k2_zfmisc_1(sK3,sK4)) | ~sP2(sK5,sK3,X0) | r1_tarski(sK3,k2_zfmisc_1(X0,sK4))) )),
% 2.21/0.68    inference(subsumption_resolution,[],[f300,f39])).
% 2.21/0.68  fof(f300,plain,(
% 2.21/0.68    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(X0,sK4)) | ~sP2(sK5,sK3,X0) | k1_xboole_0 = sK3 | sP1(sK6(sK3),sK5,k2_zfmisc_1(sK3,sK4))) )),
% 2.21/0.68    inference(resolution,[],[f157,f97])).
% 2.21/0.68  fof(f157,plain,(
% 2.21/0.68    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | r1_tarski(sK3,k2_zfmisc_1(X0,sK4)) | ~sP2(sK5,sK3,X0)) )),
% 2.21/0.68    inference(subsumption_resolution,[],[f154,f39])).
% 2.21/0.68  fof(f154,plain,(
% 2.21/0.68    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(X0,sK4)) | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~sP2(sK5,sK3,X0) | k1_xboole_0 = sK3) )),
% 2.21/0.68    inference(resolution,[],[f101,f47])).
% 2.21/0.68  fof(f47,plain,(
% 2.21/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f12])).
% 2.21/0.68  fof(f12,plain,(
% 2.21/0.68    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 2.21/0.68    inference(ennf_transformation,[],[f3])).
% 2.21/0.68  fof(f3,axiom,(
% 2.21/0.68    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 2.21/0.68  fof(f101,plain,(
% 2.21/0.68    ( ! [X0] : (r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK3)) | r1_tarski(sK3,k2_zfmisc_1(X0,sK4)) | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~sP2(sK5,sK3,X0)) )),
% 2.21/0.68    inference(superposition,[],[f63,f62])).
% 2.21/0.68  fof(f63,plain,(
% 2.21/0.68    r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK5,sK3),sK4)) | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK3)) | r1_tarski(sK3,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.21/0.68    inference(definition_unfolding,[],[f38,f52,f52,f52])).
% 2.21/0.68  fof(f52,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f5])).
% 2.21/0.68  fof(f5,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.21/0.68  fof(f38,plain,(
% 2.21/0.68    r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4)) | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3)) | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.21/0.68    inference(cnf_transformation,[],[f20])).
% 2.21/0.68  fof(f20,plain,(
% 2.21/0.68    k1_xboole_0 != sK3 & (r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4)) | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3)) | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f19])).
% 2.21/0.68  fof(f19,plain,(
% 2.21/0.68    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)))) => (k1_xboole_0 != sK3 & (r1_tarski(sK3,k3_zfmisc_1(sK5,sK3,sK4)) | r1_tarski(sK3,k3_zfmisc_1(sK4,sK5,sK3)) | r1_tarski(sK3,k3_zfmisc_1(sK3,sK4,sK5))))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f10,plain,(
% 2.21/0.68    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 2.21/0.68    inference(ennf_transformation,[],[f9])).
% 2.21/0.68  fof(f9,negated_conjecture,(
% 2.21/0.68    ~! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 2.21/0.68    inference(negated_conjecture,[],[f8])).
% 2.21/0.68  fof(f8,conjecture,(
% 2.21/0.68    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).
% 2.21/0.68  fof(f39,plain,(
% 2.21/0.68    k1_xboole_0 != sK3),
% 2.21/0.68    inference(cnf_transformation,[],[f20])).
% 2.21/0.68  % SZS output end Proof for theBenchmark
% 2.21/0.68  % (17829)------------------------------
% 2.21/0.68  % (17829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (17829)Termination reason: Refutation
% 2.21/0.68  
% 2.21/0.68  % (17829)Memory used [KB]: 2558
% 2.21/0.68  % (17829)Time elapsed: 0.271 s
% 2.21/0.68  % (17829)------------------------------
% 2.21/0.68  % (17829)------------------------------
% 2.21/0.68  % (17799)Success in time 0.308 s
%------------------------------------------------------------------------------
