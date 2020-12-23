%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 225 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   21
%              Number of atoms          :  241 ( 811 expanded)
%              Number of equality atoms :   47 ( 103 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f232,f351])).

fof(f351,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f350])).

% (7187)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f350,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f343,f51])).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f343,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl6_2 ),
    inference(backward_demodulation,[],[f30,f337])).

fof(f337,plain,
    ( k1_xboole_0 = sK0
    | spl6_2 ),
    inference(superposition,[],[f329,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f49,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f329,plain,
    ( ! [X2] : sK0 = k4_xboole_0(sK0,X2)
    | spl6_2 ),
    inference(resolution,[],[f325,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f325,plain,
    ( ! [X8] : r1_xboole_0(sK0,X8)
    | spl6_2 ),
    inference(resolution,[],[f317,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f317,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl6_2 ),
    inference(resolution,[],[f311,f29])).

fof(f29,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | ~ r2_hidden(X2,X0) )
    | spl6_2 ),
    inference(subsumption_resolution,[],[f307,f59])).

fof(f59,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f307,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | ~ r2_hidden(X2,X0)
        | r1_tarski(sK1,sK3) )
    | spl6_2 ),
    inference(resolution,[],[f252,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f252,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK5(sK1,sK3),X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,sK3))
        | ~ r2_hidden(X3,X0) )
    | spl6_2 ),
    inference(resolution,[],[f243,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f243,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,sK5(sK1,sK3)),X11)
        | ~ r1_tarski(X11,k2_zfmisc_1(X12,sK3)) )
    | spl6_2 ),
    inference(resolution,[],[f237,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f237,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl6_2 ),
    inference(resolution,[],[f234,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f234,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | spl6_2 ),
    inference(resolution,[],[f233,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ r2_hidden(sK5(sK1,sK3),X0) )
    | spl6_2 ),
    inference(resolution,[],[f59,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK5(X0,X1),X2) ) ),
    inference(resolution,[],[f40,f42])).

fof(f30,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f232,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f224,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f224,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl6_1 ),
    inference(backward_demodulation,[],[f30,f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | spl6_1 ),
    inference(superposition,[],[f210,f61])).

fof(f210,plain,
    ( ! [X2] : sK1 = k4_xboole_0(sK1,X2)
    | spl6_1 ),
    inference(resolution,[],[f199,f38])).

fof(f199,plain,
    ( ! [X8] : r1_xboole_0(sK1,X8)
    | spl6_1 ),
    inference(resolution,[],[f192,f35])).

fof(f192,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl6_1 ),
    inference(resolution,[],[f191,f29])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2))
        | ~ r2_hidden(X0,X1) )
    | spl6_1 ),
    inference(subsumption_resolution,[],[f187,f55])).

fof(f55,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2))
        | r1_tarski(sK0,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f122,f41])).

fof(f122,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK5(sK0,sK2),X0)
        | ~ r2_hidden(X3,X1)
        | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK2,X2)) )
    | spl6_1 ),
    inference(resolution,[],[f115,f48])).

fof(f115,plain,
    ( ! [X12,X10,X11] :
        ( ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X10),X11)
        | ~ r1_tarski(X11,k2_zfmisc_1(sK2,X12)) )
    | spl6_1 ),
    inference(resolution,[],[f104,f40])).

fof(f104,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2),X2),k2_zfmisc_1(sK2,X3))
    | spl6_1 ),
    inference(resolution,[],[f100,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(sK0,sK2),sK2)
    | spl6_1 ),
    inference(resolution,[],[f98,f64])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK5(sK0,sK2),X0) )
    | spl6_1 ),
    inference(resolution,[],[f66,f55])).

fof(f60,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f31,f57,f53])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (7175)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (7183)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (7175)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (7174)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (7194)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (7174)Refutation not found, incomplete strategy% (7174)------------------------------
% 0.22/0.53  % (7174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7174)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7174)Memory used [KB]: 10618
% 0.22/0.53  % (7174)Time elapsed: 0.112 s
% 0.22/0.53  % (7174)------------------------------
% 0.22/0.53  % (7174)------------------------------
% 0.22/0.53  % (7177)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (7194)Refutation not found, incomplete strategy% (7194)------------------------------
% 0.22/0.53  % (7194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7194)Memory used [KB]: 10618
% 0.22/0.53  % (7194)Time elapsed: 0.122 s
% 0.22/0.53  % (7194)------------------------------
% 0.22/0.53  % (7194)------------------------------
% 0.22/0.53  % (7176)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f60,f232,f351])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    spl6_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f350])).
% 0.22/0.54  % (7187)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f350,plain,(
% 0.22/0.54    $false | spl6_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f343,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f343,plain,(
% 0.22/0.54    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl6_2),
% 0.22/0.54    inference(backward_demodulation,[],[f30,f337])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | spl6_2),
% 0.22/0.54    inference(superposition,[],[f329,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f49,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    ( ! [X2] : (sK0 = k4_xboole_0(sK0,X2)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f325,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    ( ! [X8] : (r1_xboole_0(sK0,X8)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f317,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f311,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | ~r2_hidden(X2,X0)) ) | spl6_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f307,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK3) | spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    spl6_2 <=> r1_tarski(sK1,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | ~r2_hidden(X2,X0) | r1_tarski(sK1,sK3)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f252,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(sK1,sK3),X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,sK3)) | ~r2_hidden(X3,X0)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f243,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.54    inference(nnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    ( ! [X12,X10,X11] : (~r2_hidden(k4_tarski(X10,sK5(sK1,sK3)),X11) | ~r1_tarski(X11,k2_zfmisc_1(X12,sK3))) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f237,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f234,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ~r2_hidden(sK5(sK1,sK3),sK3) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f233,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f42,f41])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK3) | ~r2_hidden(sK5(sK1,sK3),X0)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f59,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK5(X0,X1),X2)) )),
% 0.22/0.54    inference(resolution,[],[f40,f42])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    spl6_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    $false | spl6_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f224,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl6_1),
% 0.22/0.54    inference(backward_demodulation,[],[f30,f218])).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | spl6_1),
% 0.22/0.54    inference(superposition,[],[f210,f61])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ( ! [X2] : (sK1 = k4_xboole_0(sK1,X2)) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f199,f38])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ( ! [X8] : (r1_xboole_0(sK1,X8)) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f192,f35])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f191,f29])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2)) | ~r2_hidden(X0,X1)) ) | spl6_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f187,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK2) | spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    spl6_1 <=> r1_tarski(sK0,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X2)) | r1_tarski(sK0,sK2)) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f122,f41])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(sK0,sK2),X0) | ~r2_hidden(X3,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK2,X2))) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f115,f48])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X12,X10,X11] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X10),X11) | ~r1_tarski(X11,k2_zfmisc_1(sK2,X12))) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f104,f40])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK5(sK0,sK2),X2),k2_zfmisc_1(sK2,X3))) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f100,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ~r2_hidden(sK5(sK0,sK2),sK2) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f98,f64])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r2_hidden(sK5(sK0,sK2),X0)) ) | spl6_1),
% 0.22/0.54    inference(resolution,[],[f66,f55])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ~spl6_1 | ~spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f57,f53])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (7175)------------------------------
% 0.22/0.54  % (7175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7175)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (7175)Memory used [KB]: 10874
% 0.22/0.54  % (7175)Time elapsed: 0.107 s
% 0.22/0.54  % (7175)------------------------------
% 0.22/0.54  % (7175)------------------------------
% 0.22/0.54  % (7178)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (7171)Success in time 0.179 s
%------------------------------------------------------------------------------
