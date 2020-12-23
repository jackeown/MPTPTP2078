%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:42 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 208 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  295 ( 578 expanded)
%              Number of equality atoms :   61 ( 140 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1750,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1747,f56])).

fof(f56,plain,(
    ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f1747,plain,(
    r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(superposition,[],[f1336,f1735])).

fof(f1735,plain,(
    sK3 = k3_tarski(k1_enumset1(sK2,sK2,sK3)) ),
    inference(forward_demodulation,[],[f1734,f99])).

fof(f99,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f58,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1734,plain,(
    k3_tarski(k1_enumset1(sK2,sK2,sK3)) = k3_tarski(k1_enumset1(sK3,sK3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f530,f941])).

fof(f941,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f937,f100])).

fof(f100,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f937,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0))) ),
    inference(resolution,[],[f928,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f94,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f68,f95])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f928,plain,(
    ! [X13] : sP1(X13,X13,k1_xboole_0) ),
    inference(resolution,[],[f502,f294])).

fof(f294,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f292,f215])).

fof(f215,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f80,f125])).

fof(f125,plain,(
    ! [X1] : sP0(X1,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f117,f121])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(resolution,[],[f102,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f62,f95])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f85,f95])).

fof(f85,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f33])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f290,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).

fof(f51,plain,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f290,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,X0) ),
    inference(superposition,[],[f118,f98])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f57,f96])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f118,plain,(
    ! [X0,X1] : sP1(X1,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f93,f96])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f502,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X2,X3),X3)
      | sP1(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,(
    ! [X2,X3] :
      ( sP1(X2,X2,X3)
      | r2_hidden(sK6(X2,X2,X3),X3)
      | r2_hidden(sK6(X2,X2,X3),X3)
      | sP1(X2,X2,X3) ) ),
    inference(resolution,[],[f91,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f530,plain,(
    k3_tarski(k1_enumset1(sK3,sK3,k5_xboole_0(sK2,sK2))) = k3_tarski(k1_enumset1(sK2,sK2,sK3)) ),
    inference(forward_demodulation,[],[f524,f104])).

fof(f104,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f64,f65,f65])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f524,plain,(
    k3_tarski(k1_enumset1(sK3,sK3,sK2)) = k3_tarski(k1_enumset1(sK3,sK3,k5_xboole_0(sK2,sK2))) ),
    inference(superposition,[],[f105,f259])).

fof(f259,plain,(
    sK2 = k1_setfam_1(k1_enumset1(sK2,sK2,sK3)) ),
    inference(resolution,[],[f106,f55])).

fof(f55,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f70,f95])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0))))) ),
    inference(definition_unfolding,[],[f69,f97,f96,f97])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1336,plain,(
    ! [X2,X1] : r1_tarski(k10_relat_1(sK4,X1),k10_relat_1(sK4,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(superposition,[],[f101,f548])).

fof(f548,plain,(
    ! [X0,X1] : k10_relat_1(sK4,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK4,X0),k10_relat_1(sK4,X0),k10_relat_1(sK4,X1))) ),
    inference(resolution,[],[f109,f54])).

fof(f54,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f76,f97,f97])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f61,f97])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (21793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (21777)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (21772)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (21775)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (21769)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (21770)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21785)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (21773)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (21771)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (21790)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (21782)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (21794)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (21792)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (21796)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (21768)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (21797)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (21786)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (21795)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (21774)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (21788)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (21789)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (21778)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (21787)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (21776)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (21784)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (21780)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (21781)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (21779)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (21791)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (21783)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.07/0.67  % (21774)Refutation found. Thanks to Tanya!
% 2.07/0.67  % SZS status Theorem for theBenchmark
% 2.07/0.67  % SZS output start Proof for theBenchmark
% 2.07/0.67  fof(f1750,plain,(
% 2.07/0.67    $false),
% 2.07/0.67    inference(subsumption_resolution,[],[f1747,f56])).
% 2.07/0.67  fof(f56,plain,(
% 2.07/0.67    ~r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),
% 2.07/0.67    inference(cnf_transformation,[],[f38])).
% 2.07/0.67  fof(f38,plain,(
% 2.07/0.67    ~r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f37])).
% 2.07/0.67  fof(f37,plain,(
% 2.07/0.67    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f26,plain,(
% 2.07/0.67    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.07/0.67    inference(flattening,[],[f25])).
% 2.07/0.67  fof(f25,plain,(
% 2.07/0.67    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.07/0.67    inference(ennf_transformation,[],[f23])).
% 2.07/0.67  fof(f23,negated_conjecture,(
% 2.07/0.67    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.07/0.67    inference(negated_conjecture,[],[f22])).
% 2.07/0.67  fof(f22,conjecture,(
% 2.07/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 2.07/0.67  fof(f1747,plain,(
% 2.07/0.67    r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),
% 2.07/0.67    inference(superposition,[],[f1336,f1735])).
% 2.07/0.67  fof(f1735,plain,(
% 2.07/0.67    sK3 = k3_tarski(k1_enumset1(sK2,sK2,sK3))),
% 2.07/0.67    inference(forward_demodulation,[],[f1734,f99])).
% 2.07/0.67  fof(f99,plain,(
% 2.07/0.67    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.07/0.67    inference(definition_unfolding,[],[f58,f97])).
% 2.07/0.67  fof(f97,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f67,f65])).
% 2.07/0.67  fof(f65,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f18])).
% 2.07/0.67  fof(f18,axiom,(
% 2.07/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.07/0.67  fof(f67,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.07/0.67    inference(cnf_transformation,[],[f19])).
% 2.07/0.67  fof(f19,axiom,(
% 2.07/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.07/0.67  fof(f58,plain,(
% 2.07/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.07/0.67    inference(cnf_transformation,[],[f7])).
% 2.07/0.67  fof(f7,axiom,(
% 2.07/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.07/0.67  fof(f1734,plain,(
% 2.07/0.67    k3_tarski(k1_enumset1(sK2,sK2,sK3)) = k3_tarski(k1_enumset1(sK3,sK3,k1_xboole_0))),
% 2.07/0.67    inference(forward_demodulation,[],[f530,f941])).
% 2.07/0.67  fof(f941,plain,(
% 2.07/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.07/0.67    inference(forward_demodulation,[],[f937,f100])).
% 2.07/0.67  fof(f100,plain,(
% 2.07/0.67    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 2.07/0.67    inference(definition_unfolding,[],[f60,f95])).
% 2.07/0.67  fof(f95,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f66,f65])).
% 2.07/0.67  fof(f66,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.07/0.67    inference(cnf_transformation,[],[f20])).
% 2.07/0.67  fof(f20,axiom,(
% 2.07/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.07/0.67  fof(f60,plain,(
% 2.07/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.07/0.67    inference(cnf_transformation,[],[f24])).
% 2.07/0.67  fof(f24,plain,(
% 2.07/0.67    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.07/0.67    inference(rectify,[],[f3])).
% 2.07/0.67  fof(f3,axiom,(
% 2.07/0.67    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.07/0.67  fof(f937,plain,(
% 2.07/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0)))) )),
% 2.07/0.67    inference(resolution,[],[f928,f113])).
% 2.07/0.67  fof(f113,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X2) )),
% 2.07/0.67    inference(definition_unfolding,[],[f94,f96])).
% 2.07/0.67  fof(f96,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f68,f95])).
% 2.07/0.67  fof(f68,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.07/0.67    inference(cnf_transformation,[],[f5])).
% 2.07/0.67  fof(f5,axiom,(
% 2.07/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.07/0.67  fof(f94,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f53])).
% 2.07/0.67  fof(f53,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.07/0.67    inference(nnf_transformation,[],[f36])).
% 2.07/0.67  fof(f36,plain,(
% 2.07/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 2.07/0.67    inference(definition_folding,[],[f2,f35])).
% 2.07/0.67  fof(f35,plain,(
% 2.07/0.67    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.07/0.67  fof(f2,axiom,(
% 2.07/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.07/0.67  fof(f928,plain,(
% 2.07/0.67    ( ! [X13] : (sP1(X13,X13,k1_xboole_0)) )),
% 2.07/0.67    inference(resolution,[],[f502,f294])).
% 2.07/0.67  fof(f294,plain,(
% 2.07/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.07/0.67    inference(subsumption_resolution,[],[f292,f215])).
% 2.07/0.67  fof(f215,plain,(
% 2.07/0.67    ( ! [X6,X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,X6)) )),
% 2.07/0.67    inference(resolution,[],[f80,f125])).
% 2.07/0.67  fof(f125,plain,(
% 2.07/0.67    ( ! [X1] : (sP0(X1,k1_xboole_0,k1_xboole_0)) )),
% 2.07/0.67    inference(superposition,[],[f117,f121])).
% 2.07/0.67  fof(f121,plain,(
% 2.07/0.67    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 2.07/0.67    inference(resolution,[],[f102,f59])).
% 2.07/0.67  fof(f59,plain,(
% 2.07/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.07/0.67    inference(cnf_transformation,[],[f27])).
% 2.07/0.67  fof(f27,plain,(
% 2.07/0.67    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.07/0.67    inference(ennf_transformation,[],[f13])).
% 2.07/0.67  fof(f13,axiom,(
% 2.07/0.67    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.07/0.67  fof(f102,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 2.07/0.67    inference(definition_unfolding,[],[f62,f95])).
% 2.07/0.67  fof(f62,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f6])).
% 2.07/0.67  fof(f6,axiom,(
% 2.07/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.07/0.67  fof(f117,plain,(
% 2.07/0.67    ( ! [X0,X1] : (sP0(X1,X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 2.07/0.67    inference(equality_resolution,[],[f112])).
% 2.07/0.67  fof(f112,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 2.07/0.67    inference(definition_unfolding,[],[f85,f95])).
% 2.07/0.67  fof(f85,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.07/0.67    inference(cnf_transformation,[],[f47])).
% 2.07/0.67  fof(f47,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.07/0.67    inference(nnf_transformation,[],[f34])).
% 2.07/0.67  fof(f34,plain,(
% 2.07/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.07/0.67    inference(definition_folding,[],[f1,f33])).
% 2.07/0.67  fof(f33,plain,(
% 2.07/0.67    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.07/0.67  fof(f1,axiom,(
% 2.07/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.07/0.67  fof(f80,plain,(
% 2.07/0.67    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f46])).
% 2.07/0.67  fof(f46,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.07/0.67  fof(f45,plain,(
% 2.07/0.67    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f44,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.07/0.67    inference(rectify,[],[f43])).
% 2.07/0.67  fof(f43,plain,(
% 2.07/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.07/0.67    inference(flattening,[],[f42])).
% 2.07/0.67  fof(f42,plain,(
% 2.07/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.07/0.67    inference(nnf_transformation,[],[f33])).
% 2.07/0.67  fof(f292,plain,(
% 2.07/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.07/0.67    inference(resolution,[],[f290,f88])).
% 2.07/0.67  fof(f88,plain,(
% 2.07/0.67    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f52])).
% 2.07/0.67  fof(f52,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).
% 2.07/0.67  fof(f51,plain,(
% 2.07/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f50,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.07/0.67    inference(rectify,[],[f49])).
% 2.07/0.67  fof(f49,plain,(
% 2.07/0.67    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 2.07/0.67    inference(flattening,[],[f48])).
% 2.07/0.67  fof(f48,plain,(
% 2.07/0.67    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 2.07/0.67    inference(nnf_transformation,[],[f35])).
% 2.07/0.67  fof(f290,plain,(
% 2.07/0.67    ( ! [X0] : (sP1(k1_xboole_0,X0,X0)) )),
% 2.07/0.67    inference(superposition,[],[f118,f98])).
% 2.07/0.67  fof(f98,plain,(
% 2.07/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0) )),
% 2.07/0.67    inference(definition_unfolding,[],[f57,f96])).
% 2.07/0.67  fof(f57,plain,(
% 2.07/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.07/0.67    inference(cnf_transformation,[],[f12])).
% 2.07/0.67  fof(f12,axiom,(
% 2.07/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.07/0.67  fof(f118,plain,(
% 2.07/0.67    ( ! [X0,X1] : (sP1(X1,X0,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))) )),
% 2.07/0.67    inference(equality_resolution,[],[f114])).
% 2.07/0.67  fof(f114,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2) )),
% 2.07/0.67    inference(definition_unfolding,[],[f93,f96])).
% 2.07/0.67  fof(f93,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.07/0.67    inference(cnf_transformation,[],[f53])).
% 2.07/0.67  fof(f502,plain,(
% 2.07/0.67    ( ! [X2,X3] : (r2_hidden(sK6(X2,X2,X3),X3) | sP1(X2,X2,X3)) )),
% 2.07/0.67    inference(duplicate_literal_removal,[],[f501])).
% 2.07/0.67  fof(f501,plain,(
% 2.07/0.67    ( ! [X2,X3] : (sP1(X2,X2,X3) | r2_hidden(sK6(X2,X2,X3),X3) | r2_hidden(sK6(X2,X2,X3),X3) | sP1(X2,X2,X3)) )),
% 2.07/0.67    inference(resolution,[],[f91,f90])).
% 2.07/0.67  fof(f90,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | sP1(X0,X1,X2)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f52])).
% 2.07/0.67  fof(f91,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f52])).
% 2.07/0.67  fof(f530,plain,(
% 2.07/0.67    k3_tarski(k1_enumset1(sK3,sK3,k5_xboole_0(sK2,sK2))) = k3_tarski(k1_enumset1(sK2,sK2,sK3))),
% 2.07/0.67    inference(forward_demodulation,[],[f524,f104])).
% 2.07/0.67  fof(f104,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.07/0.67    inference(definition_unfolding,[],[f64,f65,f65])).
% 2.07/0.67  fof(f64,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f17])).
% 2.07/0.67  fof(f17,axiom,(
% 2.07/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.07/0.67  fof(f524,plain,(
% 2.07/0.67    k3_tarski(k1_enumset1(sK3,sK3,sK2)) = k3_tarski(k1_enumset1(sK3,sK3,k5_xboole_0(sK2,sK2)))),
% 2.07/0.67    inference(superposition,[],[f105,f259])).
% 2.07/0.67  fof(f259,plain,(
% 2.07/0.67    sK2 = k1_setfam_1(k1_enumset1(sK2,sK2,sK3))),
% 2.07/0.67    inference(resolution,[],[f106,f55])).
% 2.07/0.67  fof(f55,plain,(
% 2.07/0.67    r1_tarski(sK2,sK3)),
% 2.07/0.67    inference(cnf_transformation,[],[f38])).
% 2.07/0.67  fof(f106,plain,(
% 2.07/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 2.07/0.67    inference(definition_unfolding,[],[f70,f95])).
% 2.07/0.67  fof(f70,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f28])).
% 2.07/0.67  fof(f28,plain,(
% 2.07/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.07/0.67    inference(ennf_transformation,[],[f9])).
% 2.07/0.67  fof(f9,axiom,(
% 2.07/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.07/0.67  fof(f105,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f69,f97,f96,f97])).
% 2.07/0.67  fof(f69,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f11])).
% 2.07/0.67  fof(f11,axiom,(
% 2.07/0.67    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.07/0.67  fof(f1336,plain,(
% 2.07/0.67    ( ! [X2,X1] : (r1_tarski(k10_relat_1(sK4,X1),k10_relat_1(sK4,k3_tarski(k1_enumset1(X1,X1,X2))))) )),
% 2.07/0.67    inference(superposition,[],[f101,f548])).
% 2.07/0.67  fof(f548,plain,(
% 2.07/0.67    ( ! [X0,X1] : (k10_relat_1(sK4,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(sK4,X0),k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)))) )),
% 2.07/0.67    inference(resolution,[],[f109,f54])).
% 2.07/0.67  fof(f54,plain,(
% 2.07/0.67    v1_relat_1(sK4)),
% 2.07/0.67    inference(cnf_transformation,[],[f38])).
% 2.07/0.67  fof(f109,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k10_relat_1(X2,X0),k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f76,f97,f97])).
% 2.07/0.67  fof(f76,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f29])).
% 2.07/0.67  fof(f29,plain,(
% 2.07/0.67    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.07/0.67    inference(ennf_transformation,[],[f21])).
% 2.07/0.67  fof(f21,axiom,(
% 2.07/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 2.07/0.67  fof(f101,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.07/0.67    inference(definition_unfolding,[],[f61,f97])).
% 2.07/0.67  fof(f61,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.07/0.67    inference(cnf_transformation,[],[f14])).
% 2.07/0.67  fof(f14,axiom,(
% 2.07/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.07/0.67  % SZS output end Proof for theBenchmark
% 2.07/0.67  % (21774)------------------------------
% 2.07/0.67  % (21774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.67  % (21774)Termination reason: Refutation
% 2.07/0.67  
% 2.07/0.67  % (21774)Memory used [KB]: 12025
% 2.07/0.67  % (21774)Time elapsed: 0.216 s
% 2.07/0.67  % (21774)------------------------------
% 2.07/0.67  % (21774)------------------------------
% 2.07/0.68  % (21767)Success in time 0.317 s
%------------------------------------------------------------------------------
