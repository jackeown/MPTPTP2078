%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:05 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 260 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  340 ( 849 expanded)
%              Number of equality atoms :   70 ( 188 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f688,plain,(
    $false ),
    inference(subsumption_resolution,[],[f687,f188])).

fof(f188,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f136,f94])).

fof(f94,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f89,f90])).

fof(f90,plain,(
    ! [X0] : sP2(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f8,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f89,plain,(
    ! [X3,X1] :
      ( ~ sP2(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(k1_xboole_0),X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f111,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f111,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f71,f107])).

fof(f107,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( X0 != X0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f76,f57])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f687,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f686,f55])).

fof(f55,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ~ v1_xboole_0(k3_xboole_0(sK3,sK4))
    & v1_zfmisc_1(sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK3,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK3,X1)) )
      & v1_zfmisc_1(sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK3,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK3,X1)) )
   => ( ~ r1_tarski(sK3,sK4)
      & ~ v1_xboole_0(k3_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f686,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f685,f116])).

fof(f116,plain,(
    sP0(sK3) ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f52,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,
    ( sP0(sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | sP0(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f63])).

fof(f63,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP1(X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f20,f26,f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ? [X1] :
          ( k6_domain_1(X0,X1) = X0
          & m1_subset_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f58,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v1_zfmisc_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v1_zfmisc_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f685,plain,
    ( ~ sP0(sK3)
    | r1_tarski(sK3,sK4)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f642,f141])).

fof(f141,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f128,f126])).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f124,f57])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f88,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f56,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f128,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK3,sK3))
    | ~ r1_xboole_0(sK3,sK4) ),
    inference(superposition,[],[f123,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f123,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4))) ),
    inference(backward_demodulation,[],[f86,f88])).

fof(f86,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f54,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f642,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X3,X4)
      | ~ sP0(X3)
      | r1_tarski(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f636])).

fof(f636,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,X4)
      | ~ sP0(X3)
      | r1_xboole_0(X3,X4)
      | ~ sP0(X3) ) ),
    inference(resolution,[],[f263,f251])).

fof(f251,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(X3),X4)
      | r1_xboole_0(X3,X4)
      | ~ sP0(X3) ) ),
    inference(subsumption_resolution,[],[f250,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f250,plain,(
    ! [X4,X3] :
      ( r1_xboole_0(X3,X4)
      | r2_hidden(sK5(X3),X4)
      | v1_xboole_0(X3)
      | ~ sP0(X3) ) ),
    inference(superposition,[],[f216,f121])).

fof(f121,plain,(
    ! [X0] :
      ( k1_tarski(sK5(X0)) = X0
      | v1_xboole_0(X0)
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ( k6_domain_1(X0,sK5(X0)) = X0
          & m1_subset_1(sK5(X0),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK5(X0)) = X0
        & m1_subset_1(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X2] :
            ( k6_domain_1(X0,X2) = X0
            & m1_subset_1(X2,X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ! [X1] :
            ( k6_domain_1(X0,X1) != X0
            | ~ m1_subset_1(X1,X0) ) )
      & ( ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f117,plain,(
    ! [X0] :
      ( k1_tarski(sK5(X0)) = X0
      | ~ m1_subset_1(sK5(X0),X0)
      | v1_xboole_0(X0)
      | ~ sP0(X0) ) ),
    inference(superposition,[],[f72,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK5(X0)) = X0
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f216,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f70,f146])).

fof(f146,plain,(
    ! [X2,X3] :
      ( sK7(k1_tarski(X2),X3) = X2
      | r1_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f112,f69])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f77,f90])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ sP2(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f263,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK5(X3),X4)
      | r1_tarski(X3,X4)
      | ~ sP0(X3) ) ),
    inference(subsumption_resolution,[],[f262,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f73,f64])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f262,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,X4)
      | ~ r2_hidden(sK5(X3),X4)
      | v1_xboole_0(X3)
      | ~ sP0(X3) ) ),
    inference(superposition,[],[f239,f121])).

fof(f239,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f74,f148])).

fof(f148,plain,(
    ! [X6,X7] :
      ( sK8(k1_tarski(X6),X7) = X6
      | r1_tarski(k1_tarski(X6),X7) ) ),
    inference(resolution,[],[f112,f73])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:19:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (4132)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (4158)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.47  % (4150)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.47  % (4141)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.48  % (4127)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.48  % (4128)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.49  % (4156)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.49  % (4145)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.50  % (4139)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.50  % (4131)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.50  % (4135)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.50  % (4158)Refutation found. Thanks to Tanya!
% 0.18/0.50  % SZS status Theorem for theBenchmark
% 0.18/0.50  % SZS output start Proof for theBenchmark
% 0.18/0.50  fof(f688,plain,(
% 0.18/0.50    $false),
% 0.18/0.50    inference(subsumption_resolution,[],[f687,f188])).
% 0.18/0.50  fof(f188,plain,(
% 0.18/0.50    v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(resolution,[],[f136,f94])).
% 0.18/0.50  fof(f94,plain,(
% 0.18/0.50    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.18/0.50    inference(resolution,[],[f89,f90])).
% 0.18/0.50  fof(f90,plain,(
% 0.18/0.50    ( ! [X0] : (sP2(X0,k1_tarski(X0))) )),
% 0.18/0.50    inference(equality_resolution,[],[f81])).
% 0.18/0.50  fof(f81,plain,(
% 0.18/0.50    ( ! [X0,X1] : (sP2(X0,X1) | k1_tarski(X0) != X1) )),
% 0.18/0.50    inference(cnf_transformation,[],[f51])).
% 0.18/0.50  fof(f51,plain,(
% 0.18/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_tarski(X0) != X1))),
% 0.18/0.50    inference(nnf_transformation,[],[f29])).
% 0.18/0.50  fof(f29,plain,(
% 0.18/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP2(X0,X1))),
% 0.18/0.50    inference(definition_folding,[],[f8,f28])).
% 0.18/0.50  fof(f28,plain,(
% 0.18/0.50    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.18/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.18/0.50  fof(f8,axiom,(
% 0.18/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.18/0.50  fof(f89,plain,(
% 0.18/0.50    ( ! [X3,X1] : (~sP2(X3,X1) | r2_hidden(X3,X1)) )),
% 0.18/0.50    inference(equality_resolution,[],[f78])).
% 0.18/0.50  fof(f78,plain,(
% 0.18/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | ~sP2(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f50])).
% 0.18/0.50  fof(f50,plain,(
% 0.18/0.50    ! [X0,X1] : ((sP2(X0,X1) | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 0.18/0.50  fof(f49,plain,(
% 0.18/0.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f48,plain,(
% 0.18/0.50    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 0.18/0.50    inference(rectify,[],[f47])).
% 0.18/0.50  fof(f47,plain,(
% 0.18/0.50    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 0.18/0.50    inference(nnf_transformation,[],[f28])).
% 0.18/0.50  fof(f136,plain,(
% 0.18/0.50    ( ! [X0] : (~r2_hidden(sK6(k1_xboole_0),X0) | v1_xboole_0(k1_xboole_0)) )),
% 0.18/0.50    inference(resolution,[],[f111,f65])).
% 0.18/0.50  fof(f65,plain,(
% 0.18/0.50    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f41])).
% 0.18/0.50  fof(f41,plain,(
% 0.18/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 0.18/0.50  fof(f40,plain,(
% 0.18/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f39,plain,(
% 0.18/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.50    inference(rectify,[],[f38])).
% 0.18/0.50  fof(f38,plain,(
% 0.18/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.50    inference(nnf_transformation,[],[f1])).
% 0.18/0.50  fof(f1,axiom,(
% 0.18/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.50  fof(f111,plain,(
% 0.18/0.50    ( ! [X6,X7] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,X7)) )),
% 0.18/0.50    inference(resolution,[],[f71,f107])).
% 0.18/0.50  fof(f107,plain,(
% 0.18/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.50    inference(trivial_inequality_removal,[],[f105])).
% 0.18/0.50  fof(f105,plain,(
% 0.18/0.50    ( ! [X0] : (X0 != X0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.50    inference(superposition,[],[f76,f57])).
% 0.18/0.50  fof(f57,plain,(
% 0.18/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.50    inference(cnf_transformation,[],[f5])).
% 0.18/0.50  fof(f5,axiom,(
% 0.18/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.18/0.50  fof(f76,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f46])).
% 0.18/0.50  fof(f46,plain,(
% 0.18/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(nnf_transformation,[],[f7])).
% 0.18/0.50  fof(f7,axiom,(
% 0.18/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.18/0.50  fof(f71,plain,(
% 0.18/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f43])).
% 0.18/0.50  fof(f43,plain,(
% 0.18/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f42])).
% 0.18/0.50  fof(f42,plain,(
% 0.18/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f21,plain,(
% 0.18/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(ennf_transformation,[],[f16])).
% 0.18/0.50  fof(f16,plain,(
% 0.18/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.50    inference(rectify,[],[f3])).
% 0.18/0.50  fof(f3,axiom,(
% 0.18/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.18/0.50  fof(f687,plain,(
% 0.18/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(subsumption_resolution,[],[f686,f55])).
% 0.18/0.50  fof(f55,plain,(
% 0.18/0.50    ~r1_tarski(sK3,sK4)),
% 0.18/0.50    inference(cnf_transformation,[],[f32])).
% 0.18/0.50  fof(f32,plain,(
% 0.18/0.50    (~r1_tarski(sK3,sK4) & ~v1_xboole_0(k3_xboole_0(sK3,sK4))) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3)),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f31,f30])).
% 0.18/0.50  fof(f30,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK3,X1) & ~v1_xboole_0(k3_xboole_0(sK3,X1))) & v1_zfmisc_1(sK3) & ~v1_xboole_0(sK3))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f31,plain,(
% 0.18/0.50    ? [X1] : (~r1_tarski(sK3,X1) & ~v1_xboole_0(k3_xboole_0(sK3,X1))) => (~r1_tarski(sK3,sK4) & ~v1_xboole_0(k3_xboole_0(sK3,sK4)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f19,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.18/0.50    inference(flattening,[],[f18])).
% 0.18/0.50  fof(f18,plain,(
% 0.18/0.50    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.18/0.50    inference(ennf_transformation,[],[f15])).
% 0.18/0.50  fof(f15,negated_conjecture,(
% 0.18/0.50    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.18/0.50    inference(negated_conjecture,[],[f14])).
% 0.18/0.50  fof(f14,conjecture,(
% 0.18/0.50    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 0.18/0.50  fof(f686,plain,(
% 0.18/0.50    r1_tarski(sK3,sK4) | ~v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(subsumption_resolution,[],[f685,f116])).
% 0.18/0.50  fof(f116,plain,(
% 0.18/0.50    sP0(sK3)),
% 0.18/0.50    inference(subsumption_resolution,[],[f115,f52])).
% 0.18/0.50  fof(f52,plain,(
% 0.18/0.50    ~v1_xboole_0(sK3)),
% 0.18/0.50    inference(cnf_transformation,[],[f32])).
% 0.18/0.50  fof(f115,plain,(
% 0.18/0.50    sP0(sK3) | v1_xboole_0(sK3)),
% 0.18/0.50    inference(resolution,[],[f91,f53])).
% 0.18/0.50  fof(f53,plain,(
% 0.18/0.50    v1_zfmisc_1(sK3)),
% 0.18/0.50    inference(cnf_transformation,[],[f32])).
% 0.18/0.50  fof(f91,plain,(
% 0.18/0.50    ( ! [X0] : (~v1_zfmisc_1(X0) | sP0(X0) | v1_xboole_0(X0)) )),
% 0.18/0.50    inference(resolution,[],[f58,f63])).
% 0.18/0.50  fof(f63,plain,(
% 0.18/0.50    ( ! [X0] : (sP1(X0) | v1_xboole_0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f27])).
% 0.18/0.50  fof(f27,plain,(
% 0.18/0.50    ! [X0] : (sP1(X0) | v1_xboole_0(X0))),
% 0.18/0.50    inference(definition_folding,[],[f20,f26,f25])).
% 0.18/0.50  fof(f25,plain,(
% 0.18/0.50    ! [X0] : (sP0(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)))),
% 0.18/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.50  fof(f26,plain,(
% 0.18/0.50    ! [X0] : ((v1_zfmisc_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.18/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.50  fof(f20,plain,(
% 0.18/0.50    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.18/0.50    inference(ennf_transformation,[],[f13])).
% 0.18/0.50  fof(f13,axiom,(
% 0.18/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.18/0.50  fof(f58,plain,(
% 0.18/0.50    ( ! [X0] : (~sP1(X0) | ~v1_zfmisc_1(X0) | sP0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f33])).
% 0.18/0.50  fof(f33,plain,(
% 0.18/0.50    ! [X0] : (((v1_zfmisc_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v1_zfmisc_1(X0))) | ~sP1(X0))),
% 0.18/0.50    inference(nnf_transformation,[],[f26])).
% 0.18/0.50  fof(f685,plain,(
% 0.18/0.50    ~sP0(sK3) | r1_tarski(sK3,sK4) | ~v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(resolution,[],[f642,f141])).
% 0.18/0.50  fof(f141,plain,(
% 0.18/0.50    ~r1_xboole_0(sK3,sK4) | ~v1_xboole_0(k1_xboole_0)),
% 0.18/0.50    inference(forward_demodulation,[],[f128,f126])).
% 0.18/0.50  fof(f126,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.18/0.50    inference(forward_demodulation,[],[f124,f57])).
% 0.18/0.50  fof(f124,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.18/0.50    inference(superposition,[],[f88,f87])).
% 0.18/0.50  fof(f87,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 0.18/0.50    inference(definition_unfolding,[],[f56,f85])).
% 0.18/0.50  fof(f85,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.18/0.50    inference(definition_unfolding,[],[f66,f84])).
% 0.18/0.50  fof(f84,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.50    inference(definition_unfolding,[],[f67,f83])).
% 0.18/0.50  fof(f83,plain,(
% 0.18/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f10])).
% 0.18/0.50  fof(f10,axiom,(
% 0.18/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.50  fof(f67,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f9])).
% 0.18/0.50  fof(f9,axiom,(
% 0.18/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.50  fof(f66,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.18/0.50    inference(cnf_transformation,[],[f11])).
% 0.18/0.50  fof(f11,axiom,(
% 0.18/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.18/0.50  fof(f56,plain,(
% 0.18/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f4])).
% 0.18/0.50  fof(f4,axiom,(
% 0.18/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.18/0.50  fof(f88,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.18/0.50    inference(definition_unfolding,[],[f68,f85])).
% 0.18/0.50  fof(f68,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f6])).
% 0.18/0.50  fof(f6,axiom,(
% 0.18/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.18/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.18/0.50  fof(f128,plain,(
% 0.18/0.50    ~v1_xboole_0(k4_xboole_0(sK3,sK3)) | ~r1_xboole_0(sK3,sK4)),
% 0.18/0.50    inference(superposition,[],[f123,f75])).
% 0.18/0.50  fof(f75,plain,(
% 0.18/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f46])).
% 0.18/0.50  fof(f123,plain,(
% 0.18/0.50    ~v1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)))),
% 0.18/0.50    inference(backward_demodulation,[],[f86,f88])).
% 0.18/0.50  fof(f86,plain,(
% 0.18/0.50    ~v1_xboole_0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))),
% 0.18/0.50    inference(definition_unfolding,[],[f54,f85])).
% 0.18/0.50  fof(f54,plain,(
% 0.18/0.50    ~v1_xboole_0(k3_xboole_0(sK3,sK4))),
% 0.18/0.50    inference(cnf_transformation,[],[f32])).
% 0.18/0.50  fof(f642,plain,(
% 0.18/0.50    ( ! [X4,X3] : (r1_xboole_0(X3,X4) | ~sP0(X3) | r1_tarski(X3,X4)) )),
% 0.18/0.50    inference(duplicate_literal_removal,[],[f636])).
% 0.18/0.50  fof(f636,plain,(
% 0.18/0.50    ( ! [X4,X3] : (r1_tarski(X3,X4) | ~sP0(X3) | r1_xboole_0(X3,X4) | ~sP0(X3)) )),
% 0.18/0.50    inference(resolution,[],[f263,f251])).
% 0.18/0.50  fof(f251,plain,(
% 0.18/0.50    ( ! [X4,X3] : (r2_hidden(sK5(X3),X4) | r1_xboole_0(X3,X4) | ~sP0(X3)) )),
% 0.18/0.50    inference(subsumption_resolution,[],[f250,f100])).
% 0.18/0.50  fof(f100,plain,(
% 0.18/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.18/0.50    inference(resolution,[],[f69,f64])).
% 0.18/0.50  fof(f64,plain,(
% 0.18/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f41])).
% 0.18/0.50  fof(f69,plain,(
% 0.18/0.50    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f43])).
% 0.18/0.50  fof(f250,plain,(
% 0.18/0.50    ( ! [X4,X3] : (r1_xboole_0(X3,X4) | r2_hidden(sK5(X3),X4) | v1_xboole_0(X3) | ~sP0(X3)) )),
% 0.18/0.50    inference(superposition,[],[f216,f121])).
% 0.18/0.50  fof(f121,plain,(
% 0.18/0.50    ( ! [X0] : (k1_tarski(sK5(X0)) = X0 | v1_xboole_0(X0) | ~sP0(X0)) )),
% 0.18/0.50    inference(subsumption_resolution,[],[f117,f60])).
% 0.18/0.50  fof(f60,plain,(
% 0.18/0.50    ( ! [X0] : (m1_subset_1(sK5(X0),X0) | ~sP0(X0)) )),
% 0.18/0.50    inference(cnf_transformation,[],[f37])).
% 0.18/0.50  fof(f37,plain,(
% 0.18/0.50    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK5(X0)) = X0 & m1_subset_1(sK5(X0),X0)) | ~sP0(X0)))),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 0.18/0.50  fof(f36,plain,(
% 0.18/0.50    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK5(X0)) = X0 & m1_subset_1(sK5(X0),X0)))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f35,plain,(
% 0.18/0.50    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~sP0(X0)))),
% 0.18/0.51    inference(rectify,[],[f34])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ! [X0] : ((sP0(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~sP0(X0)))),
% 0.18/0.51    inference(nnf_transformation,[],[f25])).
% 0.18/0.51  fof(f117,plain,(
% 0.18/0.51    ( ! [X0] : (k1_tarski(sK5(X0)) = X0 | ~m1_subset_1(sK5(X0),X0) | v1_xboole_0(X0) | ~sP0(X0)) )),
% 0.18/0.51    inference(superposition,[],[f72,f61])).
% 0.18/0.51  fof(f61,plain,(
% 0.18/0.51    ( ! [X0] : (k6_domain_1(X0,sK5(X0)) = X0 | ~sP0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f37])).
% 0.18/0.51  fof(f72,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f23])).
% 0.18/0.51  fof(f23,plain,(
% 0.18/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.18/0.51    inference(flattening,[],[f22])).
% 0.18/0.51  fof(f22,plain,(
% 0.18/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f12])).
% 0.18/0.51  fof(f12,axiom,(
% 0.18/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.18/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.18/0.51  fof(f216,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f213])).
% 0.18/0.51  fof(f213,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.18/0.51    inference(superposition,[],[f70,f146])).
% 0.18/0.51  fof(f146,plain,(
% 0.18/0.51    ( ! [X2,X3] : (sK7(k1_tarski(X2),X3) = X2 | r1_xboole_0(k1_tarski(X2),X3)) )),
% 0.18/0.51    inference(resolution,[],[f112,f69])).
% 0.18/0.51  fof(f112,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 0.18/0.51    inference(resolution,[],[f77,f90])).
% 0.18/0.51  fof(f77,plain,(
% 0.18/0.51    ( ! [X0,X3,X1] : (~sP2(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 0.18/0.51    inference(cnf_transformation,[],[f50])).
% 0.18/0.51  fof(f70,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f43])).
% 0.18/0.51  fof(f263,plain,(
% 0.18/0.51    ( ! [X4,X3] : (~r2_hidden(sK5(X3),X4) | r1_tarski(X3,X4) | ~sP0(X3)) )),
% 0.18/0.51    inference(subsumption_resolution,[],[f262,f102])).
% 0.18/0.51  fof(f102,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.18/0.51    inference(resolution,[],[f73,f64])).
% 0.18/0.51  fof(f73,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f45])).
% 0.18/0.51  fof(f45,plain,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f44])).
% 0.18/0.51  fof(f44,plain,(
% 0.18/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.18/0.51    inference(ennf_transformation,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.18/0.51    inference(unused_predicate_definition_removal,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.51  fof(f262,plain,(
% 0.18/0.51    ( ! [X4,X3] : (r1_tarski(X3,X4) | ~r2_hidden(sK5(X3),X4) | v1_xboole_0(X3) | ~sP0(X3)) )),
% 0.18/0.51    inference(superposition,[],[f239,f121])).
% 0.18/0.51  fof(f239,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.51    inference(duplicate_literal_removal,[],[f236])).
% 0.18/0.51  fof(f236,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.18/0.51    inference(superposition,[],[f74,f148])).
% 0.18/0.51  fof(f148,plain,(
% 0.18/0.51    ( ! [X6,X7] : (sK8(k1_tarski(X6),X7) = X6 | r1_tarski(k1_tarski(X6),X7)) )),
% 0.18/0.51    inference(resolution,[],[f112,f73])).
% 0.18/0.51  fof(f74,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f45])).
% 0.18/0.51  % SZS output end Proof for theBenchmark
% 0.18/0.51  % (4158)------------------------------
% 0.18/0.51  % (4158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (4158)Termination reason: Refutation
% 0.18/0.51  
% 0.18/0.51  % (4158)Memory used [KB]: 1918
% 0.18/0.51  % (4158)Time elapsed: 0.137 s
% 0.18/0.51  % (4158)------------------------------
% 0.18/0.51  % (4158)------------------------------
% 0.18/0.51  % (4126)Success in time 0.167 s
%------------------------------------------------------------------------------
