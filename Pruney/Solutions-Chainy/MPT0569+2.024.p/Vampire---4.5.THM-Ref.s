%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:29 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 282 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  418 (1061 expanded)
%              Number of equality atoms :   68 ( 211 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f116,f447,f452,f474,f495])).

fof(f495,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | spl12_1
    | ~ spl12_2 ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl12_1
    | ~ spl12_2 ),
    inference(superposition,[],[f110,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,sK2)
    | ~ spl12_2 ),
    inference(resolution,[],[f113,f398])).

fof(f398,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(sK3),X0)
      | k1_xboole_0 = k10_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f313,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f313,plain,(
    ! [X2] :
      ( r2_hidden(sK4(k2_relat_1(sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X2))),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X2)))
      | k1_xboole_0 = k10_relat_1(sK3,X2) ) ),
    inference(superposition,[],[f305,f240])).

fof(f240,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k10_relat_1(sK3,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X0))) ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK3),sK2)
      | k1_xboole_0 != k10_relat_1(sK3,sK2) )
    & ( r1_xboole_0(k2_relat_1(sK3),sK2)
      | k1_xboole_0 = k10_relat_1(sK3,sK2) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK3),sK2)
        | k1_xboole_0 != k10_relat_1(sK3,sK2) )
      & ( r1_xboole_0(k2_relat_1(sK3),sK2)
        | k1_xboole_0 = k10_relat_1(sK3,sK2) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f305,plain,(
    ! [X2] :
      ( k1_xboole_0 = k10_relat_1(sK3,X2)
      | r2_hidden(sK4(k2_relat_1(sK3),X2),X2) ) ),
    inference(resolution,[],[f303,f138])).

fof(f138,plain,(
    ! [X16] :
      ( r2_hidden(sK5(X16,k1_xboole_0),X16)
      | k1_xboole_0 = X16 ) ),
    inference(resolution,[],[f66,f117])).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f60,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK3,X0))
      | r2_hidden(sK4(k2_relat_1(sK3),X0),X0) ) ),
    inference(resolution,[],[f299,f106])).

fof(f106,plain,(
    ! [X0,X1] : sP1(X1,X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f93,f61])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f299,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ sP1(X4,X5,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X3)))
      | r2_hidden(sK4(k2_relat_1(sK3),X3),X4)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f297,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ r2_hidden(sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X1)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK11(X0,X1,X2),X0)
              & r2_hidden(sK11(X0,X1,X2),X1) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X1)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X0)
            & r2_hidden(sK11(X0,X1,X2),X1) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f297,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k2_relat_1(sK3),X1),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1)))
      | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f292,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f63,f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(sK3),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f248,f96])).

fof(f248,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK9(X2,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1)),sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1)))
      | ~ r2_hidden(X2,k10_relat_1(sK3,X1)) ) ),
    inference(superposition,[],[f188,f240])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
      | r2_hidden(sK9(X0,X1,sK3),X1) ) ),
    inference(resolution,[],[f77,f57])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK9(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
            & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
        & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f113,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_2
  <=> r1_xboole_0(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f110,plain,
    ( k1_xboole_0 != k10_relat_1(sK3,sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl12_1
  <=> k1_xboole_0 = k10_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f474,plain,
    ( ~ spl12_1
    | spl12_2
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl12_1
    | spl12_2
    | ~ spl12_9 ),
    inference(resolution,[],[f464,f117])).

fof(f464,plain,
    ( r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k1_xboole_0)
    | ~ spl12_1
    | spl12_2
    | ~ spl12_9 ),
    inference(forward_demodulation,[],[f463,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f463,plain,
    ( r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,sK2))
    | spl12_2
    | ~ spl12_9 ),
    inference(forward_demodulation,[],[f454,f240])).

fof(f454,plain,
    ( r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2))))
    | spl12_2
    | ~ spl12_9 ),
    inference(resolution,[],[f446,f223])).

fof(f223,plain,
    ( r2_hidden(sK4(k2_relat_1(sK3),sK2),k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2)))
    | spl12_2 ),
    inference(resolution,[],[f114,f97])).

fof(f114,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),sK2)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),X0)
        | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0)) )
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl12_9
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),X0)
        | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f452,plain,
    ( spl12_2
    | spl12_8 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl12_2
    | spl12_8 ),
    inference(resolution,[],[f443,f239])).

fof(f239,plain,
    ( r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3))
    | spl12_2 ),
    inference(resolution,[],[f229,f106])).

fof(f229,plain,
    ( ! [X2,X3] :
        ( ~ sP1(X3,X2,k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2)))
        | r2_hidden(sK4(k2_relat_1(sK3),sK2),X2) )
    | spl12_2 ),
    inference(resolution,[],[f223,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f443,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3))
    | spl12_8 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl12_8
  <=> r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f447,plain,
    ( ~ spl12_8
    | spl12_9
    | spl12_2 ),
    inference(avatar_split_clause,[],[f435,f112,f445,f441])).

fof(f435,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),X0)
        | ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3))
        | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0)) )
    | spl12_2 ),
    inference(resolution,[],[f434,f241])).

fof(f241,plain,
    ( r2_hidden(k4_tarski(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),sK4(k2_relat_1(sK3),sK2)),sK3)
    | spl12_2 ),
    inference(resolution,[],[f239,f102])).

fof(f102,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f434,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK3)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(X2,k10_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f78,f57])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f58,f112,f108])).

fof(f58,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2)
    | k1_xboole_0 = k10_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f59,f112,f108])).

fof(f59,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK3),sK2)
    | k1_xboole_0 != k10_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:22:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (18876)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (18869)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (18873)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18870)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (18872)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18878)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (18885)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (18875)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18889)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (18871)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (18886)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (18895)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18892)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (18877)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (18882)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (18893)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (18894)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (18880)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18897)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (18884)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (18891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (18891)Refutation not found, incomplete strategy% (18891)------------------------------
% 0.21/0.54  % (18891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18891)Memory used [KB]: 10746
% 0.21/0.54  % (18891)Time elapsed: 0.128 s
% 0.21/0.54  % (18891)------------------------------
% 0.21/0.54  % (18891)------------------------------
% 0.21/0.55  % (18881)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18898)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (18879)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (18890)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (18883)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (18887)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (18874)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (18888)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (18896)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.88/0.60  % (18881)Refutation found. Thanks to Tanya!
% 1.88/0.60  % SZS status Theorem for theBenchmark
% 1.88/0.60  % SZS output start Proof for theBenchmark
% 1.88/0.60  fof(f496,plain,(
% 1.88/0.60    $false),
% 1.88/0.60    inference(avatar_sat_refutation,[],[f115,f116,f447,f452,f474,f495])).
% 1.88/0.60  fof(f495,plain,(
% 1.88/0.60    spl12_1 | ~spl12_2),
% 1.88/0.60    inference(avatar_contradiction_clause,[],[f494])).
% 1.88/0.60  fof(f494,plain,(
% 1.88/0.60    $false | (spl12_1 | ~spl12_2)),
% 1.88/0.60    inference(trivial_inequality_removal,[],[f491])).
% 1.88/0.61  fof(f491,plain,(
% 1.88/0.61    k1_xboole_0 != k1_xboole_0 | (spl12_1 | ~spl12_2)),
% 1.88/0.61    inference(superposition,[],[f110,f475])).
% 1.88/0.61  fof(f475,plain,(
% 1.88/0.61    k1_xboole_0 = k10_relat_1(sK3,sK2) | ~spl12_2),
% 1.88/0.61    inference(resolution,[],[f113,f398])).
% 1.88/0.61  fof(f398,plain,(
% 1.88/0.61    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK3),X0) | k1_xboole_0 = k10_relat_1(sK3,X0)) )),
% 1.88/0.61    inference(resolution,[],[f313,f96])).
% 1.88/0.61  fof(f96,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(definition_unfolding,[],[f64,f61])).
% 1.88/0.61  fof(f61,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f8])).
% 1.88/0.61  fof(f8,axiom,(
% 1.88/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.88/0.61  fof(f64,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f29])).
% 1.88/0.61  fof(f29,plain,(
% 1.88/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f28])).
% 1.88/0.61  fof(f28,plain,(
% 1.88/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f16,plain,(
% 1.88/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f14])).
% 1.88/0.61  fof(f14,plain,(
% 1.88/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.88/0.61    inference(rectify,[],[f4])).
% 1.88/0.61  fof(f4,axiom,(
% 1.88/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.88/0.61  fof(f313,plain,(
% 1.88/0.61    ( ! [X2] : (r2_hidden(sK4(k2_relat_1(sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X2))),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X2))) | k1_xboole_0 = k10_relat_1(sK3,X2)) )),
% 1.88/0.61    inference(superposition,[],[f305,f240])).
% 1.88/0.61  fof(f240,plain,(
% 1.88/0.61    ( ! [X0] : (k10_relat_1(sK3,X0) = k10_relat_1(sK3,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X0)))) )),
% 1.88/0.61    inference(resolution,[],[f98,f57])).
% 1.88/0.61  fof(f57,plain,(
% 1.88/0.61    v1_relat_1(sK3)),
% 1.88/0.61    inference(cnf_transformation,[],[f27])).
% 1.88/0.61  fof(f27,plain,(
% 1.88/0.61    (~r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 != k10_relat_1(sK3,sK2)) & (r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 = k10_relat_1(sK3,sK2)) & v1_relat_1(sK3)),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f26])).
% 1.88/0.61  fof(f26,plain,(
% 1.88/0.61    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 != k10_relat_1(sK3,sK2)) & (r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 = k10_relat_1(sK3,sK2)) & v1_relat_1(sK3))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f25,plain,(
% 1.88/0.61    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.88/0.61    inference(flattening,[],[f24])).
% 1.88/0.61  fof(f24,plain,(
% 1.88/0.61    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.88/0.61    inference(nnf_transformation,[],[f15])).
% 1.88/0.61  fof(f15,plain,(
% 1.88/0.61    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.88/0.61    inference(ennf_transformation,[],[f13])).
% 1.88/0.61  fof(f13,negated_conjecture,(
% 1.88/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.88/0.61    inference(negated_conjecture,[],[f12])).
% 1.88/0.61  fof(f12,conjecture,(
% 1.88/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.88/0.61  fof(f98,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f65,f61])).
% 1.88/0.61  fof(f65,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f17])).
% 1.88/0.61  fof(f17,plain,(
% 1.88/0.61    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.88/0.61    inference(ennf_transformation,[],[f11])).
% 1.88/0.61  fof(f11,axiom,(
% 1.88/0.61    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.88/0.61  fof(f305,plain,(
% 1.88/0.61    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK3,X2) | r2_hidden(sK4(k2_relat_1(sK3),X2),X2)) )),
% 1.88/0.61    inference(resolution,[],[f303,f138])).
% 1.88/0.61  fof(f138,plain,(
% 1.88/0.61    ( ! [X16] : (r2_hidden(sK5(X16,k1_xboole_0),X16) | k1_xboole_0 = X16) )),
% 1.88/0.61    inference(resolution,[],[f66,f117])).
% 1.88/0.61  fof(f117,plain,(
% 1.88/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.88/0.61    inference(superposition,[],[f60,f103])).
% 1.88/0.61  fof(f103,plain,(
% 1.88/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.88/0.61    inference(equality_resolution,[],[f74])).
% 1.88/0.61  fof(f74,plain,(
% 1.88/0.61    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.88/0.61    inference(cnf_transformation,[],[f40])).
% 1.88/0.61  fof(f40,plain,(
% 1.88/0.61    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.88/0.61    inference(flattening,[],[f39])).
% 1.88/0.61  fof(f39,plain,(
% 1.88/0.61    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.88/0.61    inference(nnf_transformation,[],[f6])).
% 1.88/0.61  fof(f6,axiom,(
% 1.88/0.61    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.88/0.61  fof(f60,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f7])).
% 1.88/0.61  fof(f7,axiom,(
% 1.88/0.61    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.88/0.61  fof(f66,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | X0 = X1 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f32])).
% 1.88/0.61  fof(f32,plain,(
% 1.88/0.61    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.88/0.61  fof(f31,plain,(
% 1.88/0.61    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f30,plain,(
% 1.88/0.61    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.88/0.61    inference(nnf_transformation,[],[f18])).
% 1.88/0.61  fof(f18,plain,(
% 1.88/0.61    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.88/0.61    inference(ennf_transformation,[],[f3])).
% 1.88/0.61  fof(f3,axiom,(
% 1.88/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.88/0.61  fof(f303,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k10_relat_1(sK3,X0)) | r2_hidden(sK4(k2_relat_1(sK3),X0),X0)) )),
% 1.88/0.61    inference(resolution,[],[f299,f106])).
% 1.88/0.61  fof(f106,plain,(
% 1.88/0.61    ( ! [X0,X1] : (sP1(X1,X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.88/0.61    inference(equality_resolution,[],[f100])).
% 1.88/0.61  fof(f100,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.88/0.61    inference(definition_unfolding,[],[f93,f61])).
% 1.88/0.61  fof(f93,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.88/0.61    inference(cnf_transformation,[],[f56])).
% 1.88/0.61  fof(f56,plain,(
% 1.88/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.88/0.61    inference(nnf_transformation,[],[f23])).
% 1.88/0.61  fof(f23,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.88/0.61    inference(definition_folding,[],[f1,f22])).
% 1.88/0.61  fof(f22,plain,(
% 1.88/0.61    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.88/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.88/0.61  fof(f1,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.88/0.61  fof(f299,plain,(
% 1.88/0.61    ( ! [X4,X2,X5,X3] : (~sP1(X4,X5,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X3))) | r2_hidden(sK4(k2_relat_1(sK3),X3),X4) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 1.88/0.61    inference(resolution,[],[f297,f88])).
% 1.88/0.61  fof(f88,plain,(
% 1.88/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP1(X0,X1,X2)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f55])).
% 1.88/0.61  fof(f55,plain,(
% 1.88/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~r2_hidden(sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X1) | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1)) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f53,f54])).
% 1.88/0.61  fof(f54,plain,(
% 1.88/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X1) | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK11(X0,X1,X2),X1)) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f53,plain,(
% 1.88/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.88/0.61    inference(rectify,[],[f52])).
% 1.88/0.61  fof(f52,plain,(
% 1.88/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.88/0.61    inference(flattening,[],[f51])).
% 1.88/0.61  fof(f51,plain,(
% 1.88/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.88/0.61    inference(nnf_transformation,[],[f22])).
% 1.88/0.61  fof(f297,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r2_hidden(sK4(k2_relat_1(sK3),X1),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1))) | ~r2_hidden(X0,k10_relat_1(sK3,X1))) )),
% 1.88/0.61    inference(resolution,[],[f292,f97])).
% 1.88/0.61  fof(f97,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.88/0.61    inference(definition_unfolding,[],[f63,f61])).
% 1.88/0.61  fof(f63,plain,(
% 1.88/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f29])).
% 1.88/0.61  fof(f292,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(sK3),X1) | ~r2_hidden(X0,k10_relat_1(sK3,X1))) )),
% 1.88/0.61    inference(resolution,[],[f248,f96])).
% 1.88/0.61  fof(f248,plain,(
% 1.88/0.61    ( ! [X2,X1] : (r2_hidden(sK9(X2,k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1)),sK3),k1_setfam_1(k2_tarski(k2_relat_1(sK3),X1))) | ~r2_hidden(X2,k10_relat_1(sK3,X1))) )),
% 1.88/0.61    inference(superposition,[],[f188,f240])).
% 1.88/0.61  fof(f188,plain,(
% 1.88/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK3,X1)) | r2_hidden(sK9(X0,X1,sK3),X1)) )),
% 1.88/0.61    inference(resolution,[],[f77,f57])).
% 1.88/0.61  fof(f77,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK9(X0,X1,X2),X1)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f44])).
% 1.88/0.61  fof(f44,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).
% 1.88/0.61  fof(f43,plain,(
% 1.88/0.61    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) & r2_hidden(sK9(X0,X1,X2),k2_relat_1(X2))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f42,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.88/0.61    inference(rectify,[],[f41])).
% 1.88/0.61  fof(f41,plain,(
% 1.88/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.88/0.61    inference(nnf_transformation,[],[f19])).
% 1.88/0.61  fof(f19,plain,(
% 1.88/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.88/0.61    inference(ennf_transformation,[],[f10])).
% 1.88/0.61  fof(f10,axiom,(
% 1.88/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.88/0.61  fof(f113,plain,(
% 1.88/0.61    r1_xboole_0(k2_relat_1(sK3),sK2) | ~spl12_2),
% 1.88/0.61    inference(avatar_component_clause,[],[f112])).
% 1.88/0.61  fof(f112,plain,(
% 1.88/0.61    spl12_2 <=> r1_xboole_0(k2_relat_1(sK3),sK2)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.88/0.61  fof(f110,plain,(
% 1.88/0.61    k1_xboole_0 != k10_relat_1(sK3,sK2) | spl12_1),
% 1.88/0.61    inference(avatar_component_clause,[],[f108])).
% 1.88/0.61  fof(f108,plain,(
% 1.88/0.61    spl12_1 <=> k1_xboole_0 = k10_relat_1(sK3,sK2)),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.88/0.61  fof(f474,plain,(
% 1.88/0.61    ~spl12_1 | spl12_2 | ~spl12_9),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f469])).
% 1.88/0.61  fof(f469,plain,(
% 1.88/0.61    $false | (~spl12_1 | spl12_2 | ~spl12_9)),
% 1.88/0.61    inference(resolution,[],[f464,f117])).
% 1.88/0.61  fof(f464,plain,(
% 1.88/0.61    r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k1_xboole_0) | (~spl12_1 | spl12_2 | ~spl12_9)),
% 1.88/0.61    inference(forward_demodulation,[],[f463,f109])).
% 1.88/0.61  fof(f109,plain,(
% 1.88/0.61    k1_xboole_0 = k10_relat_1(sK3,sK2) | ~spl12_1),
% 1.88/0.61    inference(avatar_component_clause,[],[f108])).
% 1.88/0.61  fof(f463,plain,(
% 1.88/0.61    r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,sK2)) | (spl12_2 | ~spl12_9)),
% 1.88/0.61    inference(forward_demodulation,[],[f454,f240])).
% 1.88/0.61  fof(f454,plain,(
% 1.88/0.61    r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2)))) | (spl12_2 | ~spl12_9)),
% 1.88/0.61    inference(resolution,[],[f446,f223])).
% 1.88/0.61  fof(f223,plain,(
% 1.88/0.61    r2_hidden(sK4(k2_relat_1(sK3),sK2),k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2))) | spl12_2),
% 1.88/0.61    inference(resolution,[],[f114,f97])).
% 1.88/0.61  fof(f114,plain,(
% 1.88/0.61    ~r1_xboole_0(k2_relat_1(sK3),sK2) | spl12_2),
% 1.88/0.61    inference(avatar_component_clause,[],[f112])).
% 1.88/0.61  fof(f446,plain,(
% 1.88/0.61    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK3),sK2),X0) | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0))) ) | ~spl12_9),
% 1.88/0.61    inference(avatar_component_clause,[],[f445])).
% 1.88/0.61  fof(f445,plain,(
% 1.88/0.61    spl12_9 <=> ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK3),sK2),X0) | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0)))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.88/0.61  fof(f452,plain,(
% 1.88/0.61    spl12_2 | spl12_8),
% 1.88/0.61    inference(avatar_contradiction_clause,[],[f448])).
% 1.88/0.61  fof(f448,plain,(
% 1.88/0.61    $false | (spl12_2 | spl12_8)),
% 1.88/0.61    inference(resolution,[],[f443,f239])).
% 1.88/0.61  fof(f239,plain,(
% 1.88/0.61    r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) | spl12_2),
% 1.88/0.61    inference(resolution,[],[f229,f106])).
% 1.88/0.61  fof(f229,plain,(
% 1.88/0.61    ( ! [X2,X3] : (~sP1(X3,X2,k1_setfam_1(k2_tarski(k2_relat_1(sK3),sK2))) | r2_hidden(sK4(k2_relat_1(sK3),sK2),X2)) ) | spl12_2),
% 1.88/0.61    inference(resolution,[],[f223,f87])).
% 1.88/0.61  fof(f87,plain,(
% 1.88/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP1(X0,X1,X2)) )),
% 1.88/0.61    inference(cnf_transformation,[],[f55])).
% 1.88/0.61  fof(f443,plain,(
% 1.88/0.61    ~r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) | spl12_8),
% 1.88/0.61    inference(avatar_component_clause,[],[f441])).
% 1.88/0.61  fof(f441,plain,(
% 1.88/0.61    spl12_8 <=> r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3))),
% 1.88/0.61    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.88/0.61  fof(f447,plain,(
% 1.88/0.61    ~spl12_8 | spl12_9 | spl12_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f435,f112,f445,f441])).
% 1.88/0.61  fof(f435,plain,(
% 1.88/0.61    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK3),sK2),X0) | ~r2_hidden(sK4(k2_relat_1(sK3),sK2),k2_relat_1(sK3)) | r2_hidden(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),k10_relat_1(sK3,X0))) ) | spl12_2),
% 1.88/0.61    inference(resolution,[],[f434,f241])).
% 1.88/0.61  fof(f241,plain,(
% 1.88/0.61    r2_hidden(k4_tarski(sK8(sK3,sK4(k2_relat_1(sK3),sK2)),sK4(k2_relat_1(sK3),sK2)),sK3) | spl12_2),
% 1.88/0.61    inference(resolution,[],[f239,f102])).
% 1.88/0.61  fof(f102,plain,(
% 1.88/0.61    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)) )),
% 1.88/0.61    inference(equality_resolution,[],[f68])).
% 1.88/0.61  fof(f68,plain,(
% 1.88/0.61    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.88/0.61    inference(cnf_transformation,[],[f38])).
% 1.88/0.61  fof(f38,plain,(
% 1.88/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.88/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f34,f37,f36,f35])).
% 1.88/0.61  fof(f35,plain,(
% 1.88/0.61    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f36,plain,(
% 1.88/0.61    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f37,plain,(
% 1.88/0.61    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 1.88/0.61    introduced(choice_axiom,[])).
% 1.88/0.61  fof(f34,plain,(
% 1.88/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.88/0.61    inference(rectify,[],[f33])).
% 1.88/0.61  fof(f33,plain,(
% 1.88/0.61    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.88/0.61    inference(nnf_transformation,[],[f9])).
% 1.88/0.61  fof(f9,axiom,(
% 1.88/0.61    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.88/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.88/0.61  fof(f434,plain,(
% 1.88/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK3) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X2,k10_relat_1(sK3,X1))) )),
% 1.88/0.61    inference(resolution,[],[f78,f57])).
% 1.88/0.61  fof(f78,plain,(
% 1.88/0.61    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.88/0.61    inference(cnf_transformation,[],[f44])).
% 1.88/0.61  fof(f116,plain,(
% 1.88/0.61    spl12_1 | spl12_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f58,f112,f108])).
% 1.88/0.61  fof(f58,plain,(
% 1.88/0.61    r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 = k10_relat_1(sK3,sK2)),
% 1.88/0.61    inference(cnf_transformation,[],[f27])).
% 1.88/0.61  fof(f115,plain,(
% 1.88/0.61    ~spl12_1 | ~spl12_2),
% 1.88/0.61    inference(avatar_split_clause,[],[f59,f112,f108])).
% 1.88/0.61  fof(f59,plain,(
% 1.88/0.61    ~r1_xboole_0(k2_relat_1(sK3),sK2) | k1_xboole_0 != k10_relat_1(sK3,sK2)),
% 1.88/0.61    inference(cnf_transformation,[],[f27])).
% 1.88/0.61  % SZS output end Proof for theBenchmark
% 1.88/0.61  % (18881)------------------------------
% 1.88/0.61  % (18881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (18881)Termination reason: Refutation
% 1.88/0.61  
% 1.88/0.61  % (18881)Memory used [KB]: 6524
% 1.88/0.61  % (18881)Time elapsed: 0.214 s
% 1.88/0.61  % (18881)------------------------------
% 1.88/0.61  % (18881)------------------------------
% 1.88/0.61  % (18868)Success in time 0.248 s
%------------------------------------------------------------------------------
