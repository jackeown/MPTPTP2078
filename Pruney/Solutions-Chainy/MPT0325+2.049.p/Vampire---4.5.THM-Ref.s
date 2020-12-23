%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 332 expanded)
%              Number of leaves         :   18 (  91 expanded)
%              Depth                    :   25
%              Number of atoms          :  269 ( 779 expanded)
%              Number of equality atoms :  126 ( 363 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f1177,f2377,f2725,f3019,f3046,f3089,f3289])).

fof(f3289,plain,
    ( spl4_10
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f3288])).

fof(f3288,plain,
    ( $false
    | spl4_10
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f3287])).

fof(f3287,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_10
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(superposition,[],[f3020,f3018])).

fof(f3018,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f3016])).

fof(f3016,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f3020,plain,
    ( k1_xboole_0 != sK0
    | spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f1168,f2992])).

fof(f2992,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_12 ),
    inference(equality_resolution,[],[f1176])).

fof(f1176,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1168,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1167,plain,
    ( spl4_10
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f3089,plain,
    ( spl4_2
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f3086])).

fof(f3086,plain,
    ( $false
    | spl4_2
    | ~ spl4_19 ),
    inference(resolution,[],[f3077,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3077,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f3076])).

fof(f3076,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f3063,f67])).

fof(f67,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f64,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f64,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3063,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl4_19 ),
    inference(superposition,[],[f40,f3055])).

fof(f3055,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_19 ),
    inference(equality_resolution,[],[f3014])).

fof(f3014,plain,
    ( ! [X10,X11] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11)
        | k3_xboole_0(sK1,sK3) = X11 )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f3013])).

fof(f3013,plain,
    ( spl4_19
  <=> ! [X11,X10] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11)
        | k3_xboole_0(sK1,sK3) = X11 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3046,plain,
    ( spl4_1
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f3043])).

fof(f3043,plain,
    ( $false
    | spl4_1
    | ~ spl4_12 ),
    inference(resolution,[],[f3038,f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f3038,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f3037])).

fof(f3037,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f3024,f67])).

fof(f3024,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f40,f2992])).

fof(f3019,plain,
    ( spl4_11
    | spl4_19
    | spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f3011,f1175,f3016,f3013,f1171])).

fof(f1171,plain,
    ( spl4_11
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f3011,plain,
    ( ! [X10,X11] :
        ( k1_xboole_0 = sK0
        | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X11 )
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f3007,f2992])).

fof(f3007,plain,(
    ! [X10,X11] :
      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | k3_xboole_0(sK1,sK3) = X11 ) ),
    inference(superposition,[],[f340,f51])).

fof(f51,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f19])).

fof(f19,plain,
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f340,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( k2_zfmisc_1(X7,X8) != k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))
      | k1_xboole_0 = k3_xboole_0(X5,X6)
      | k1_xboole_0 = k3_xboole_0(X3,X4)
      | k3_xboole_0(X5,X6) = X8 ) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f2725,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f2724])).

fof(f2724,plain,
    ( $false
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f2705])).

fof(f2705,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_10 ),
    inference(superposition,[],[f24,f1209])).

fof(f1209,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f51,f1208])).

fof(f1208,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f1181,f84])).

fof(f84,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f83,f26])).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ) ),
    inference(superposition,[],[f74,f26])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X2)
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1181,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))
    | ~ spl4_10 ),
    inference(superposition,[],[f34,f1169])).

fof(f1169,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f24,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f2377,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f2376])).

fof(f2376,plain,
    ( $false
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f2357])).

fof(f2357,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_11 ),
    inference(superposition,[],[f24,f1753])).

fof(f1753,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f51,f1752])).

fof(f1752,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f1731,f761])).

fof(f761,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f738,f26])).

fof(f738,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f731,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f34,f26])).

fof(f731,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f729,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f729,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f728,f84])).

fof(f728,plain,(
    ! [X0] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f726])).

fof(f726,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(superposition,[],[f722,f26])).

fof(f722,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f721,f26])).

fof(f721,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k1_xboole_0,k1_xboole_0))
      | k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f717,f84])).

fof(f717,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)) ) ),
    inference(superposition,[],[f426,f26])).

fof(f426,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X2,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)) ) ),
    inference(resolution,[],[f179,f31])).

fof(f179,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_xboole_0(X12,k3_xboole_0(X11,k1_xboole_0))
      | r1_xboole_0(k2_zfmisc_1(X12,X13),k3_xboole_0(k2_zfmisc_1(X11,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)) ) ),
    inference(superposition,[],[f37,f137])).

fof(f137,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,k1_xboole_0),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f113,f84])).

fof(f113,plain,(
    ! [X4,X3] : k3_xboole_0(k2_zfmisc_1(X3,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(k3_xboole_0(X3,X4),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f34,f51])).

fof(f1731,plain,
    ( ! [X2,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))
    | ~ spl4_11 ),
    inference(superposition,[],[f34,f1173])).

fof(f1173,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f1177,plain,
    ( spl4_10
    | spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f1160,f1175,f1171,f1167])).

fof(f1160,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2)
      | k3_xboole_0(sK0,sK2) = X0 ) ),
    inference(superposition,[],[f189,f51])).

fof(f189,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( k2_zfmisc_1(X7,X8) != k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))
      | k1_xboole_0 = k3_xboole_0(X5,X6)
      | k1_xboole_0 = k3_xboole_0(X3,X4)
      | k3_xboole_0(X3,X4) = X7 ) ),
    inference(superposition,[],[f35,f34])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f46,f42])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (15063)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15051)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (15079)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (15055)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.55  % (15071)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.56  % (15062)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (15058)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.56  % (15070)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (15054)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.54/0.57  % (15052)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.54/0.57  % (15078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.54/0.58  % (15064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.58  % (15069)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.58  % (15077)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.60  % (15056)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.54/0.60  % (15061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.54/0.60  % (15075)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.61  % (15073)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.61  % (15067)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.61  % (15065)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.54/0.61  % (15080)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.54/0.61  % (15053)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.54/0.61  % (15059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.54/0.62  % (15073)Refutation not found, incomplete strategy% (15073)------------------------------
% 1.54/0.62  % (15073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.62  % (15073)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.62  
% 1.54/0.62  % (15073)Memory used [KB]: 10618
% 1.54/0.62  % (15073)Time elapsed: 0.136 s
% 1.54/0.62  % (15073)------------------------------
% 1.54/0.62  % (15073)------------------------------
% 1.54/0.62  % (15074)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.63  % (15057)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.54/0.63  % (15066)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.63  % (15068)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.12/0.64  % (15072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.12/0.64  % (15066)Refutation not found, incomplete strategy% (15066)------------------------------
% 2.12/0.64  % (15066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (15066)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.65  
% 2.12/0.65  % (15066)Memory used [KB]: 6268
% 2.12/0.65  % (15066)Time elapsed: 0.157 s
% 2.12/0.65  % (15066)------------------------------
% 2.12/0.65  % (15066)------------------------------
% 2.12/0.65  % (15068)Refutation not found, incomplete strategy% (15068)------------------------------
% 2.12/0.65  % (15068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (15068)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.65  
% 2.12/0.65  % (15068)Memory used [KB]: 10618
% 2.12/0.65  % (15068)Time elapsed: 0.229 s
% 2.12/0.65  % (15068)------------------------------
% 2.12/0.65  % (15068)------------------------------
% 2.12/0.66  % (15060)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.12/0.67  % (15076)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 3.00/0.77  % (15063)Refutation found. Thanks to Tanya!
% 3.00/0.77  % SZS status Theorem for theBenchmark
% 3.00/0.77  % SZS output start Proof for theBenchmark
% 3.00/0.77  fof(f3290,plain,(
% 3.00/0.77    $false),
% 3.00/0.77    inference(avatar_sat_refutation,[],[f49,f1177,f2377,f2725,f3019,f3046,f3089,f3289])).
% 3.00/0.77  fof(f3289,plain,(
% 3.00/0.77    spl4_10 | ~spl4_12 | ~spl4_20),
% 3.00/0.77    inference(avatar_contradiction_clause,[],[f3288])).
% 3.00/0.77  fof(f3288,plain,(
% 3.00/0.77    $false | (spl4_10 | ~spl4_12 | ~spl4_20)),
% 3.00/0.77    inference(trivial_inequality_removal,[],[f3287])).
% 3.00/0.77  fof(f3287,plain,(
% 3.00/0.77    k1_xboole_0 != k1_xboole_0 | (spl4_10 | ~spl4_12 | ~spl4_20)),
% 3.00/0.77    inference(superposition,[],[f3020,f3018])).
% 3.00/0.77  fof(f3018,plain,(
% 3.00/0.77    k1_xboole_0 = sK0 | ~spl4_20),
% 3.00/0.77    inference(avatar_component_clause,[],[f3016])).
% 3.00/0.77  fof(f3016,plain,(
% 3.00/0.77    spl4_20 <=> k1_xboole_0 = sK0),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 3.00/0.77  fof(f3020,plain,(
% 3.00/0.77    k1_xboole_0 != sK0 | (spl4_10 | ~spl4_12)),
% 3.00/0.77    inference(superposition,[],[f1168,f2992])).
% 3.00/0.77  fof(f2992,plain,(
% 3.00/0.77    sK0 = k3_xboole_0(sK0,sK2) | ~spl4_12),
% 3.00/0.77    inference(equality_resolution,[],[f1176])).
% 3.00/0.77  fof(f1176,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0) ) | ~spl4_12),
% 3.00/0.77    inference(avatar_component_clause,[],[f1175])).
% 3.00/0.77  fof(f1175,plain,(
% 3.00/0.77    spl4_12 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.00/0.77  fof(f1168,plain,(
% 3.00/0.77    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl4_10),
% 3.00/0.77    inference(avatar_component_clause,[],[f1167])).
% 3.00/0.77  fof(f1167,plain,(
% 3.00/0.77    spl4_10 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.00/0.77  fof(f3089,plain,(
% 3.00/0.77    spl4_2 | ~spl4_19),
% 3.00/0.77    inference(avatar_contradiction_clause,[],[f3086])).
% 3.00/0.77  fof(f3086,plain,(
% 3.00/0.77    $false | (spl4_2 | ~spl4_19)),
% 3.00/0.77    inference(resolution,[],[f3077,f48])).
% 3.00/0.77  fof(f48,plain,(
% 3.00/0.77    ~r1_tarski(sK1,sK3) | spl4_2),
% 3.00/0.77    inference(avatar_component_clause,[],[f46])).
% 3.00/0.77  fof(f46,plain,(
% 3.00/0.77    spl4_2 <=> r1_tarski(sK1,sK3)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.00/0.77  fof(f3077,plain,(
% 3.00/0.77    r1_tarski(sK1,sK3) | ~spl4_19),
% 3.00/0.77    inference(trivial_inequality_removal,[],[f3076])).
% 3.00/0.77  fof(f3076,plain,(
% 3.00/0.77    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl4_19),
% 3.00/0.77    inference(forward_demodulation,[],[f3063,f67])).
% 3.00/0.77  fof(f67,plain,(
% 3.00/0.77    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 3.00/0.77    inference(forward_demodulation,[],[f64,f26])).
% 3.00/0.77  fof(f26,plain,(
% 3.00/0.77    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.00/0.77    inference(cnf_transformation,[],[f12])).
% 3.00/0.77  fof(f12,plain,(
% 3.00/0.77    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.00/0.77    inference(rectify,[],[f2])).
% 3.00/0.77  fof(f2,axiom,(
% 3.00/0.77    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.00/0.77  fof(f64,plain,(
% 3.00/0.77    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 3.00/0.77    inference(resolution,[],[f39,f50])).
% 3.00/0.77  fof(f50,plain,(
% 3.00/0.77    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.00/0.77    inference(superposition,[],[f27,f26])).
% 3.00/0.77  fof(f27,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f5])).
% 3.00/0.77  fof(f5,axiom,(
% 3.00/0.77    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.00/0.77  fof(f39,plain,(
% 3.00/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.00/0.77    inference(definition_unfolding,[],[f33,f28])).
% 3.00/0.77  fof(f28,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f4])).
% 3.00/0.77  fof(f4,axiom,(
% 3.00/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.00/0.77  fof(f33,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f22])).
% 3.00/0.77  fof(f22,plain,(
% 3.00/0.77    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.00/0.77    inference(nnf_transformation,[],[f3])).
% 3.00/0.77  fof(f3,axiom,(
% 3.00/0.77    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.00/0.77  fof(f3063,plain,(
% 3.00/0.77    k1_xboole_0 != k5_xboole_0(sK1,sK1) | r1_tarski(sK1,sK3) | ~spl4_19),
% 3.00/0.77    inference(superposition,[],[f40,f3055])).
% 3.00/0.77  fof(f3055,plain,(
% 3.00/0.77    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_19),
% 3.00/0.77    inference(equality_resolution,[],[f3014])).
% 3.00/0.77  fof(f3014,plain,(
% 3.00/0.77    ( ! [X10,X11] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11) | k3_xboole_0(sK1,sK3) = X11) ) | ~spl4_19),
% 3.00/0.77    inference(avatar_component_clause,[],[f3013])).
% 3.00/0.77  fof(f3013,plain,(
% 3.00/0.77    spl4_19 <=> ! [X11,X10] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11) | k3_xboole_0(sK1,sK3) = X11)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.00/0.77  fof(f40,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 3.00/0.77    inference(definition_unfolding,[],[f32,f28])).
% 3.00/0.77  fof(f32,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f22])).
% 3.00/0.77  fof(f3046,plain,(
% 3.00/0.77    spl4_1 | ~spl4_12),
% 3.00/0.77    inference(avatar_contradiction_clause,[],[f3043])).
% 3.00/0.77  fof(f3043,plain,(
% 3.00/0.77    $false | (spl4_1 | ~spl4_12)),
% 3.00/0.77    inference(resolution,[],[f3038,f44])).
% 3.00/0.77  fof(f44,plain,(
% 3.00/0.77    ~r1_tarski(sK0,sK2) | spl4_1),
% 3.00/0.77    inference(avatar_component_clause,[],[f42])).
% 3.00/0.77  fof(f42,plain,(
% 3.00/0.77    spl4_1 <=> r1_tarski(sK0,sK2)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.00/0.77  fof(f3038,plain,(
% 3.00/0.77    r1_tarski(sK0,sK2) | ~spl4_12),
% 3.00/0.77    inference(trivial_inequality_removal,[],[f3037])).
% 3.00/0.77  fof(f3037,plain,(
% 3.00/0.77    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl4_12),
% 3.00/0.77    inference(forward_demodulation,[],[f3024,f67])).
% 3.00/0.77  fof(f3024,plain,(
% 3.00/0.77    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK2) | ~spl4_12),
% 3.00/0.77    inference(superposition,[],[f40,f2992])).
% 3.00/0.77  fof(f3019,plain,(
% 3.00/0.77    spl4_11 | spl4_19 | spl4_20 | ~spl4_12),
% 3.00/0.77    inference(avatar_split_clause,[],[f3011,f1175,f3016,f3013,f1171])).
% 3.00/0.77  fof(f1171,plain,(
% 3.00/0.77    spl4_11 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.00/0.77  fof(f3011,plain,(
% 3.00/0.77    ( ! [X10,X11] : (k1_xboole_0 = sK0 | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X11) ) | ~spl4_12),
% 3.00/0.77    inference(forward_demodulation,[],[f3007,f2992])).
% 3.00/0.77  fof(f3007,plain,(
% 3.00/0.77    ( ! [X10,X11] : (k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X10,X11) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k3_xboole_0(sK1,sK3) = X11) )),
% 3.00/0.77    inference(superposition,[],[f340,f51])).
% 3.00/0.77  fof(f51,plain,(
% 3.00/0.77    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.00/0.77    inference(resolution,[],[f29,f23])).
% 3.00/0.77  fof(f23,plain,(
% 3.00/0.77    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.00/0.77    inference(cnf_transformation,[],[f20])).
% 3.00/0.77  fof(f20,plain,(
% 3.00/0.77    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.00/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f19])).
% 3.00/0.77  fof(f19,plain,(
% 3.00/0.77    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 3.00/0.77    introduced(choice_axiom,[])).
% 3.00/0.77  fof(f14,plain,(
% 3.00/0.77    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.00/0.77    inference(flattening,[],[f13])).
% 3.00/0.77  fof(f13,plain,(
% 3.00/0.77    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.00/0.77    inference(ennf_transformation,[],[f11])).
% 3.00/0.77  fof(f11,negated_conjecture,(
% 3.00/0.77    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.00/0.77    inference(negated_conjecture,[],[f10])).
% 3.00/0.77  fof(f10,conjecture,(
% 3.00/0.77    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.00/0.77  fof(f29,plain,(
% 3.00/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.00/0.77    inference(cnf_transformation,[],[f15])).
% 3.00/0.77  fof(f15,plain,(
% 3.00/0.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.00/0.77    inference(ennf_transformation,[],[f6])).
% 3.00/0.77  fof(f6,axiom,(
% 3.00/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.00/0.77  fof(f340,plain,(
% 3.00/0.77    ( ! [X6,X4,X8,X7,X5,X3] : (k2_zfmisc_1(X7,X8) != k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) | k1_xboole_0 = k3_xboole_0(X5,X6) | k1_xboole_0 = k3_xboole_0(X3,X4) | k3_xboole_0(X5,X6) = X8) )),
% 3.00/0.77    inference(superposition,[],[f36,f34])).
% 3.00/0.77  fof(f34,plain,(
% 3.00/0.77    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f7])).
% 3.00/0.77  fof(f7,axiom,(
% 3.00/0.77    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.00/0.77  fof(f36,plain,(
% 3.00/0.77    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 3.00/0.77    inference(cnf_transformation,[],[f17])).
% 3.00/0.77  fof(f17,plain,(
% 3.00/0.77    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 3.00/0.77    inference(flattening,[],[f16])).
% 3.00/0.77  fof(f16,plain,(
% 3.00/0.77    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 3.00/0.77    inference(ennf_transformation,[],[f9])).
% 3.00/0.77  fof(f9,axiom,(
% 3.00/0.77    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 3.00/0.77  fof(f2725,plain,(
% 3.00/0.77    ~spl4_10),
% 3.00/0.77    inference(avatar_contradiction_clause,[],[f2724])).
% 3.00/0.77  fof(f2724,plain,(
% 3.00/0.77    $false | ~spl4_10),
% 3.00/0.77    inference(trivial_inequality_removal,[],[f2705])).
% 3.00/0.77  fof(f2705,plain,(
% 3.00/0.77    k1_xboole_0 != k1_xboole_0 | ~spl4_10),
% 3.00/0.77    inference(superposition,[],[f24,f1209])).
% 3.00/0.77  fof(f1209,plain,(
% 3.00/0.77    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_10),
% 3.00/0.77    inference(backward_demodulation,[],[f51,f1208])).
% 3.00/0.77  fof(f1208,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))) ) | ~spl4_10),
% 3.00/0.77    inference(forward_demodulation,[],[f1181,f84])).
% 3.00/0.77  fof(f84,plain,(
% 3.00/0.77    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 3.00/0.77    inference(superposition,[],[f83,f26])).
% 3.00/0.77  fof(f83,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X1))) )),
% 3.00/0.77    inference(equality_resolution,[],[f80])).
% 3.00/0.77  fof(f80,plain,(
% 3.00/0.77    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) )),
% 3.00/0.77    inference(superposition,[],[f74,f26])).
% 3.00/0.78  fof(f74,plain,(
% 3.00/0.78    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k3_xboole_0(X0,X2) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.00/0.78    inference(resolution,[],[f60,f31])).
% 3.00/0.78  fof(f31,plain,(
% 3.00/0.78    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.00/0.78    inference(cnf_transformation,[],[f21])).
% 3.00/0.78  fof(f21,plain,(
% 3.00/0.78    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.00/0.78    inference(nnf_transformation,[],[f1])).
% 3.00/0.78  fof(f1,axiom,(
% 3.00/0.78    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.00/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.00/0.78  fof(f60,plain,(
% 3.00/0.78    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.00/0.78    inference(resolution,[],[f37,f30])).
% 3.00/0.78  fof(f30,plain,(
% 3.00/0.78    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.00/0.78    inference(cnf_transformation,[],[f21])).
% 3.00/0.78  fof(f37,plain,(
% 3.00/0.78    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.78    inference(cnf_transformation,[],[f18])).
% 3.00/0.78  fof(f18,plain,(
% 3.00/0.78    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.78    inference(ennf_transformation,[],[f8])).
% 3.00/0.78  fof(f8,axiom,(
% 3.00/0.78    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.00/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 3.00/0.78  fof(f1181,plain,(
% 3.00/0.78    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X1))) ) | ~spl4_10),
% 3.00/0.78    inference(superposition,[],[f34,f1169])).
% 3.00/0.78  fof(f1169,plain,(
% 3.00/0.78    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_10),
% 3.00/0.78    inference(avatar_component_clause,[],[f1167])).
% 3.00/0.79  fof(f24,plain,(
% 3.00/0.79    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 3.00/0.79    inference(cnf_transformation,[],[f20])).
% 3.00/0.79  fof(f2377,plain,(
% 3.00/0.79    ~spl4_11),
% 3.00/0.79    inference(avatar_contradiction_clause,[],[f2376])).
% 3.00/0.79  fof(f2376,plain,(
% 3.00/0.79    $false | ~spl4_11),
% 3.00/0.79    inference(trivial_inequality_removal,[],[f2357])).
% 3.00/0.79  fof(f2357,plain,(
% 3.00/0.79    k1_xboole_0 != k1_xboole_0 | ~spl4_11),
% 3.00/0.79    inference(superposition,[],[f24,f1753])).
% 3.00/0.79  fof(f1753,plain,(
% 3.00/0.79    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_11),
% 3.00/0.79    inference(backward_demodulation,[],[f51,f1752])).
% 3.00/0.79  fof(f1752,plain,(
% 3.00/0.79    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))) ) | ~spl4_11),
% 3.00/0.79    inference(forward_demodulation,[],[f1731,f761])).
% 3.00/0.79  fof(f761,plain,(
% 3.00/0.79    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) )),
% 3.00/0.79    inference(forward_demodulation,[],[f738,f26])).
% 3.00/0.79  fof(f738,plain,(
% 3.00/0.79    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k3_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 3.00/0.79    inference(superposition,[],[f731,f109])).
% 3.00/0.79  fof(f109,plain,(
% 3.00/0.79    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 3.00/0.79    inference(superposition,[],[f34,f26])).
% 3.00/0.79  fof(f731,plain,(
% 3.00/0.79    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,k1_xboole_0))) )),
% 3.00/0.79    inference(resolution,[],[f729,f61])).
% 3.00/0.79  fof(f61,plain,(
% 3.00/0.79    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) )),
% 3.00/0.79    inference(resolution,[],[f38,f30])).
% 3.00/0.79  fof(f38,plain,(
% 3.00/0.79    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 3.00/0.79    inference(cnf_transformation,[],[f18])).
% 3.00/0.79  fof(f729,plain,(
% 3.00/0.79    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.00/0.79    inference(forward_demodulation,[],[f728,f84])).
% 3.00/0.79  fof(f728,plain,(
% 3.00/0.79    ( ! [X0] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 3.00/0.79    inference(trivial_inequality_removal,[],[f726])).
% 3.00/0.79  fof(f726,plain,(
% 3.00/0.79    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 3.00/0.79    inference(superposition,[],[f722,f26])).
% 3.00/0.79  fof(f722,plain,(
% 3.00/0.79    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0)) )),
% 3.00/0.79    inference(forward_demodulation,[],[f721,f26])).
% 3.00/0.79  fof(f721,plain,(
% 3.00/0.79    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0)) )),
% 3.00/0.79    inference(forward_demodulation,[],[f717,f84])).
% 3.00/0.79  fof(f717,plain,(
% 3.00/0.79    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0))) )),
% 3.00/0.79    inference(superposition,[],[f426,f26])).
% 3.00/0.79  fof(f426,plain,(
% 3.00/0.79    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X2,k2_zfmisc_1(sK0,sK1)),k1_xboole_0))) )),
% 3.00/0.79    inference(resolution,[],[f179,f31])).
% 3.00/0.79  fof(f179,plain,(
% 3.00/0.79    ( ! [X12,X13,X11] : (~r1_xboole_0(X12,k3_xboole_0(X11,k1_xboole_0)) | r1_xboole_0(k2_zfmisc_1(X12,X13),k3_xboole_0(k2_zfmisc_1(X11,k2_zfmisc_1(sK0,sK1)),k1_xboole_0))) )),
% 3.00/0.79    inference(superposition,[],[f37,f137])).
% 3.00/0.79  fof(f137,plain,(
% 3.00/0.79    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(X0,k1_xboole_0),k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)) )),
% 3.00/0.79    inference(superposition,[],[f113,f84])).
% 3.00/0.79  fof(f113,plain,(
% 3.00/0.79    ( ! [X4,X3] : (k3_xboole_0(k2_zfmisc_1(X3,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(k3_xboole_0(X3,X4),k2_zfmisc_1(sK0,sK1))) )),
% 3.00/0.79    inference(superposition,[],[f34,f51])).
% 3.00/0.79  fof(f1731,plain,(
% 3.00/0.79    ( ! [X2,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,sK3))) ) | ~spl4_11),
% 3.00/0.79    inference(superposition,[],[f34,f1173])).
% 3.00/0.79  fof(f1173,plain,(
% 3.00/0.79    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_11),
% 3.00/0.79    inference(avatar_component_clause,[],[f1171])).
% 3.00/0.79  fof(f1177,plain,(
% 3.00/0.79    spl4_10 | spl4_11 | spl4_12),
% 3.00/0.79    inference(avatar_split_clause,[],[f1160,f1175,f1171,f1167])).
% 3.00/0.79  fof(f1160,plain,(
% 3.00/0.79    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k3_xboole_0(sK0,sK2) = X0) )),
% 3.00/0.79    inference(superposition,[],[f189,f51])).
% 3.00/0.79  fof(f189,plain,(
% 3.00/0.79    ( ! [X6,X4,X8,X7,X5,X3] : (k2_zfmisc_1(X7,X8) != k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) | k1_xboole_0 = k3_xboole_0(X5,X6) | k1_xboole_0 = k3_xboole_0(X3,X4) | k3_xboole_0(X3,X4) = X7) )),
% 3.00/0.79    inference(superposition,[],[f35,f34])).
% 3.00/0.79  fof(f35,plain,(
% 3.00/0.79    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 3.00/0.79    inference(cnf_transformation,[],[f17])).
% 3.00/0.79  fof(f49,plain,(
% 3.00/0.79    ~spl4_1 | ~spl4_2),
% 3.00/0.79    inference(avatar_split_clause,[],[f25,f46,f42])).
% 3.00/0.79  fof(f25,plain,(
% 3.00/0.79    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 3.00/0.79    inference(cnf_transformation,[],[f20])).
% 3.00/0.79  % SZS output end Proof for theBenchmark
% 3.00/0.79  % (15063)------------------------------
% 3.00/0.79  % (15063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.79  % (15063)Termination reason: Refutation
% 3.00/0.79  
% 3.00/0.79  % (15063)Memory used [KB]: 7547
% 3.00/0.79  % (15063)Time elapsed: 0.343 s
% 3.00/0.79  % (15063)------------------------------
% 3.00/0.79  % (15063)------------------------------
% 3.00/0.79  % (15050)Success in time 0.43 s
%------------------------------------------------------------------------------
