%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 428 expanded)
%              Number of leaves         :   29 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  396 (1497 expanded)
%              Number of equality atoms :  100 ( 538 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f168,f203,f224,f245,f248,f301,f308,f334,f346,f390,f403,f410,f456,f462,f515,f538])).

fof(f538,plain,
    ( ~ spl14_2
    | ~ spl14_17 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_17 ),
    inference(trivial_inequality_removal,[],[f536])).

fof(f536,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl14_2
    | ~ spl14_17 ),
    inference(superposition,[],[f50,f517])).

fof(f517,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_2
    | ~ spl14_17 ),
    inference(backward_demodulation,[],[f93,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK4
    | ~ spl14_17 ),
    inference(resolution,[],[f307,f143])).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(sK8(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f141,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f141,plain,(
    ! [X1] :
      ( r2_xboole_0(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f104,f100])).

fof(f100,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f99,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f99,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r2_xboole_0(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f307,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK4)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl14_17
  <=> ! [X6] : ~ r2_hidden(X6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f93,plain,
    ( sK2 = sK4
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl14_2
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK2 != sK4
      | sK1 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21])).

fof(f21,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f515,plain,
    ( ~ spl14_12
    | ~ spl14_16 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | ~ spl14_12
    | ~ spl14_16 ),
    inference(resolution,[],[f512,f492])).

fof(f492,plain,
    ( r2_hidden(sK8(sK1,sK3),sK3)
    | ~ spl14_12 ),
    inference(resolution,[],[f240,f67])).

fof(f240,plain,
    ( r2_xboole_0(sK1,sK3)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl14_12
  <=> r2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f512,plain,
    ( ~ r2_hidden(sK8(sK1,sK3),sK3)
    | ~ spl14_12
    | ~ spl14_16 ),
    inference(resolution,[],[f328,f240])).

fof(f328,plain,
    ( ! [X3] :
        ( ~ r2_xboole_0(sK1,X3)
        | ~ r2_hidden(sK8(sK1,X3),sK3) )
    | ~ spl14_16 ),
    inference(resolution,[],[f304,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f304,plain,
    ( ! [X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(X7,sK3) )
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl14_16
  <=> ! [X7] :
        ( ~ r2_hidden(X7,sK3)
        | r2_hidden(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f462,plain,
    ( spl14_10
    | spl14_2
    | ~ spl14_11 ),
    inference(avatar_split_clause,[],[f460,f221,f92,f217])).

fof(f217,plain,
    ( spl14_10
  <=> r2_xboole_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f221,plain,
    ( spl14_11
  <=> r1_tarski(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f460,plain,
    ( sK2 = sK4
    | r2_xboole_0(sK2,sK4)
    | ~ spl14_11 ),
    inference(resolution,[],[f223,f63])).

fof(f223,plain,
    ( r1_tarski(sK2,sK4)
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f221])).

fof(f456,plain,(
    ~ spl14_9 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl14_9 ),
    inference(trivial_inequality_removal,[],[f454])).

fof(f454,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl14_9 ),
    inference(superposition,[],[f50,f432])).

fof(f432,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_9 ),
    inference(resolution,[],[f174,f143])).

fof(f174,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK2)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl14_9
  <=> ! [X10] : ~ r2_hidden(X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f410,plain,(
    ~ spl14_19 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl14_19 ),
    inference(trivial_inequality_removal,[],[f408])).

fof(f408,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl14_19 ),
    inference(superposition,[],[f49,f389])).

fof(f389,plain,
    ( k1_xboole_0 = sK1
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl14_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f403,plain,(
    ~ spl14_18 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl14_18 ),
    inference(trivial_inequality_removal,[],[f401])).

fof(f401,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl14_18 ),
    inference(superposition,[],[f50,f385])).

fof(f385,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl14_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f390,plain,
    ( spl14_18
    | spl14_19
    | ~ spl14_15 ),
    inference(avatar_split_clause,[],[f379,f299,f387,f383])).

fof(f299,plain,
    ( spl14_15
  <=> ! [X5] : ~ r2_hidden(X5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f379,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl14_15 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl14_15 ),
    inference(superposition,[],[f64,f362])).

fof(f362,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl14_15 ),
    inference(forward_demodulation,[],[f347,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f347,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k1_xboole_0,sK4)
    | ~ spl14_15 ),
    inference(backward_demodulation,[],[f48,f341])).

fof(f341,plain,
    ( k1_xboole_0 = sK3
    | ~ spl14_15 ),
    inference(resolution,[],[f300,f143])).

fof(f300,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK3)
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f299])).

fof(f48,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f346,plain,
    ( spl14_9
    | spl14_8 ),
    inference(avatar_split_clause,[],[f292,f170,f173])).

fof(f170,plain,
    ( spl14_8
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK1)
        | r2_hidden(X11,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f292,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f110,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f79,f48])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f334,plain,
    ( ~ spl14_10
    | ~ spl14_14 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(resolution,[],[f331,f225])).

fof(f225,plain,
    ( r2_hidden(sK8(sK2,sK4),sK4)
    | ~ spl14_10 ),
    inference(resolution,[],[f219,f67])).

fof(f219,plain,
    ( r2_xboole_0(sK2,sK4)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f217])).

fof(f331,plain,
    ( ~ r2_hidden(sK8(sK2,sK4),sK4)
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(resolution,[],[f324,f219])).

fof(f324,plain,
    ( ! [X3] :
        ( ~ r2_xboole_0(sK2,X3)
        | ~ r2_hidden(sK8(sK2,X3),sK4) )
    | ~ spl14_14 ),
    inference(resolution,[],[f276,f68])).

fof(f276,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK2)
        | ~ r2_hidden(X3,sK4) )
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl14_14
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK4)
        | r2_hidden(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f308,plain,
    ( spl14_16
    | spl14_17 ),
    inference(avatar_split_clause,[],[f297,f306,f303])).

fof(f297,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X7,sK3)
      | r2_hidden(X7,sK1) ) ),
    inference(resolution,[],[f159,f79])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f81,f48])).

fof(f301,plain,
    ( spl14_15
    | spl14_14 ),
    inference(avatar_split_clause,[],[f296,f275,f299])).

fof(f296,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(X5,sK3)
      | r2_hidden(X4,sK2) ) ),
    inference(resolution,[],[f159,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f248,plain,
    ( spl14_12
    | spl14_1
    | ~ spl14_13 ),
    inference(avatar_split_clause,[],[f246,f242,f88,f238])).

fof(f88,plain,
    ( spl14_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f242,plain,
    ( spl14_13
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f246,plain,
    ( sK1 = sK3
    | r2_xboole_0(sK1,sK3)
    | ~ spl14_13 ),
    inference(resolution,[],[f244,f63])).

fof(f244,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f245,plain,
    ( spl14_1
    | spl14_12
    | spl14_13
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f235,f170,f242,f238,f88])).

fof(f235,plain,
    ( r1_tarski(sK1,sK3)
    | r2_xboole_0(sK1,sK3)
    | sK1 = sK3
    | ~ spl14_8 ),
    inference(resolution,[],[f212,f104])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,sK3),sK1)
        | r1_tarski(X0,sK3) )
    | ~ spl14_8 ),
    inference(resolution,[],[f171,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f171,plain,
    ( ! [X11] :
        ( r2_hidden(X11,sK3)
        | ~ r2_hidden(X11,sK1) )
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f224,plain,
    ( spl14_2
    | spl14_10
    | spl14_11
    | ~ spl14_7 ),
    inference(avatar_split_clause,[],[f214,f166,f221,f217,f92])).

fof(f166,plain,
    ( spl14_7
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK2)
        | r2_hidden(X8,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f214,plain,
    ( r1_tarski(sK2,sK4)
    | r2_xboole_0(sK2,sK4)
    | sK2 = sK4
    | ~ spl14_7 ),
    inference(resolution,[],[f210,f104])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(X0,sK4),sK2)
        | r1_tarski(X0,sK4) )
    | ~ spl14_7 ),
    inference(resolution,[],[f167,f60])).

fof(f167,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK4)
        | ~ r2_hidden(X8,sK2) )
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f203,plain,(
    ~ spl14_6 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl14_6 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl14_6 ),
    inference(superposition,[],[f49,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | ~ spl14_6 ),
    inference(resolution,[],[f164,f143])).

fof(f164,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK1)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl14_6
  <=> ! [X9] : ~ r2_hidden(X9,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f168,plain,
    ( spl14_6
    | spl14_7 ),
    inference(avatar_split_clause,[],[f157,f166,f163])).

fof(f157,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK2)
      | ~ r2_hidden(X9,sK1)
      | r2_hidden(X8,sK4) ) ),
    inference(resolution,[],[f81,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X1,sK4) ) ),
    inference(superposition,[],[f80,f48])).

fof(f95,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f51,f92,f88])).

fof(f51,plain,
    ( sK2 != sK4
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:02:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17871)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (17879)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (17884)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (17867)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (17867)Refutation not found, incomplete strategy% (17867)------------------------------
% 0.22/0.52  % (17867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17867)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17867)Memory used [KB]: 1663
% 0.22/0.52  % (17867)Time elapsed: 0.104 s
% 0.22/0.52  % (17867)------------------------------
% 0.22/0.52  % (17867)------------------------------
% 0.22/0.52  % (17876)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (17894)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (17872)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (17883)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (17887)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.53  % (17874)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (17873)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  % (17870)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (17895)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (17868)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (17896)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.54  % (17886)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.54  % (17891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.54  % (17898)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.54  % (17899)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.55  % (17882)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.55  % (17897)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.55  % (17893)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.55  % (17888)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.55  % (17889)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.55  % (17881)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.55  % (17878)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.55  % (17875)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.55  % (17880)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (17877)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (17880)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % (17885)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (17885)Refutation not found, incomplete strategy% (17885)------------------------------
% 1.50/0.56  % (17885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (17885)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (17885)Memory used [KB]: 10618
% 1.50/0.56  % (17885)Time elapsed: 0.158 s
% 1.50/0.56  % (17885)------------------------------
% 1.50/0.56  % (17885)------------------------------
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f539,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(avatar_sat_refutation,[],[f95,f168,f203,f224,f245,f248,f301,f308,f334,f346,f390,f403,f410,f456,f462,f515,f538])).
% 1.50/0.59  fof(f538,plain,(
% 1.50/0.59    ~spl14_2 | ~spl14_17),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f537])).
% 1.50/0.59  fof(f537,plain,(
% 1.50/0.59    $false | (~spl14_2 | ~spl14_17)),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f536])).
% 1.50/0.59  fof(f536,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | (~spl14_2 | ~spl14_17)),
% 1.50/0.59    inference(superposition,[],[f50,f517])).
% 1.50/0.59  fof(f517,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | (~spl14_2 | ~spl14_17)),
% 1.50/0.59    inference(backward_demodulation,[],[f93,f316])).
% 1.50/0.59  fof(f316,plain,(
% 1.50/0.59    k1_xboole_0 = sK4 | ~spl14_17),
% 1.50/0.59    inference(resolution,[],[f307,f143])).
% 1.50/0.59  fof(f143,plain,(
% 1.50/0.59    ( ! [X0] : (r2_hidden(sK8(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 1.50/0.59    inference(resolution,[],[f141,f67])).
% 1.50/0.59  fof(f67,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK8(X0,X1),X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f38])).
% 1.50/0.59  fof(f38,plain,(
% 1.50/0.59    ! [X0,X1] : ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f37])).
% 1.50/0.59  fof(f37,plain,(
% 1.50/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f18,plain,(
% 1.50/0.59    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.50/0.59    inference(ennf_transformation,[],[f5])).
% 1.50/0.59  fof(f5,axiom,(
% 1.50/0.59    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.50/0.59  fof(f141,plain,(
% 1.50/0.59    ( ! [X1] : (r2_xboole_0(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 1.50/0.59    inference(resolution,[],[f104,f100])).
% 1.50/0.59  fof(f100,plain,(
% 1.50/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(forward_demodulation,[],[f99,f53])).
% 1.50/0.59  fof(f53,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f6])).
% 1.50/0.59  fof(f6,axiom,(
% 1.50/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.50/0.59  fof(f99,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.50/0.59    inference(resolution,[],[f57,f52])).
% 1.50/0.59  fof(f52,plain,(
% 1.50/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f7])).
% 1.50/0.59  fof(f7,axiom,(
% 1.50/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.50/0.59  fof(f57,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f28])).
% 1.50/0.59  fof(f28,plain,(
% 1.50/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f27])).
% 1.50/0.59  fof(f27,plain,(
% 1.50/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f16,plain,(
% 1.50/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(ennf_transformation,[],[f13])).
% 1.50/0.59  fof(f13,plain,(
% 1.50/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(rectify,[],[f4])).
% 1.50/0.59  fof(f4,axiom,(
% 1.50/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.50/0.59  fof(f104,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r2_xboole_0(X0,X1) | X0 = X1) )),
% 1.50/0.59    inference(resolution,[],[f63,f59])).
% 1.50/0.59  fof(f59,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f32])).
% 1.50/0.59  fof(f32,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).
% 1.50/0.59  fof(f31,plain,(
% 1.50/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f30,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(rectify,[],[f29])).
% 1.50/0.59  fof(f29,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f17])).
% 1.50/0.59  fof(f17,plain,(
% 1.50/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.59    inference(ennf_transformation,[],[f2])).
% 1.50/0.59  fof(f2,axiom,(
% 1.50/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.59  fof(f63,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f34])).
% 1.50/0.59  fof(f34,plain,(
% 1.50/0.59    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.50/0.59    inference(flattening,[],[f33])).
% 1.50/0.59  fof(f33,plain,(
% 1.50/0.59    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f3])).
% 1.50/0.59  fof(f3,axiom,(
% 1.50/0.59    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.50/0.59  fof(f307,plain,(
% 1.50/0.59    ( ! [X6] : (~r2_hidden(X6,sK4)) ) | ~spl14_17),
% 1.50/0.59    inference(avatar_component_clause,[],[f306])).
% 1.50/0.59  fof(f306,plain,(
% 1.50/0.59    spl14_17 <=> ! [X6] : ~r2_hidden(X6,sK4)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 1.50/0.59  fof(f93,plain,(
% 1.50/0.59    sK2 = sK4 | ~spl14_2),
% 1.50/0.59    inference(avatar_component_clause,[],[f92])).
% 1.50/0.59  fof(f92,plain,(
% 1.50/0.59    spl14_2 <=> sK2 = sK4),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 1.50/0.59  fof(f50,plain,(
% 1.50/0.59    k1_xboole_0 != sK2),
% 1.50/0.59    inference(cnf_transformation,[],[f22])).
% 1.50/0.59  fof(f22,plain,(
% 1.50/0.59    (sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f21])).
% 1.50/0.59  fof(f21,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f15,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.50/0.59    inference(flattening,[],[f14])).
% 1.50/0.59  fof(f14,plain,(
% 1.50/0.59    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.50/0.59    inference(ennf_transformation,[],[f12])).
% 1.50/0.59  fof(f12,negated_conjecture,(
% 1.50/0.59    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.59    inference(negated_conjecture,[],[f11])).
% 1.50/0.59  fof(f11,conjecture,(
% 1.50/0.59    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.50/0.59  fof(f515,plain,(
% 1.50/0.59    ~spl14_12 | ~spl14_16),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f513])).
% 1.50/0.59  fof(f513,plain,(
% 1.50/0.59    $false | (~spl14_12 | ~spl14_16)),
% 1.50/0.59    inference(resolution,[],[f512,f492])).
% 1.50/0.59  fof(f492,plain,(
% 1.50/0.59    r2_hidden(sK8(sK1,sK3),sK3) | ~spl14_12),
% 1.50/0.59    inference(resolution,[],[f240,f67])).
% 1.50/0.59  fof(f240,plain,(
% 1.50/0.59    r2_xboole_0(sK1,sK3) | ~spl14_12),
% 1.50/0.59    inference(avatar_component_clause,[],[f238])).
% 1.50/0.59  fof(f238,plain,(
% 1.50/0.59    spl14_12 <=> r2_xboole_0(sK1,sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 1.50/0.59  fof(f512,plain,(
% 1.50/0.59    ~r2_hidden(sK8(sK1,sK3),sK3) | (~spl14_12 | ~spl14_16)),
% 1.50/0.59    inference(resolution,[],[f328,f240])).
% 1.50/0.59  fof(f328,plain,(
% 1.50/0.59    ( ! [X3] : (~r2_xboole_0(sK1,X3) | ~r2_hidden(sK8(sK1,X3),sK3)) ) | ~spl14_16),
% 1.50/0.59    inference(resolution,[],[f304,f68])).
% 1.50/0.59  fof(f68,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f38])).
% 1.50/0.59  fof(f304,plain,(
% 1.50/0.59    ( ! [X7] : (r2_hidden(X7,sK1) | ~r2_hidden(X7,sK3)) ) | ~spl14_16),
% 1.50/0.59    inference(avatar_component_clause,[],[f303])).
% 1.50/0.59  fof(f303,plain,(
% 1.50/0.59    spl14_16 <=> ! [X7] : (~r2_hidden(X7,sK3) | r2_hidden(X7,sK1))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).
% 1.50/0.59  fof(f462,plain,(
% 1.50/0.59    spl14_10 | spl14_2 | ~spl14_11),
% 1.50/0.59    inference(avatar_split_clause,[],[f460,f221,f92,f217])).
% 1.50/0.59  fof(f217,plain,(
% 1.50/0.59    spl14_10 <=> r2_xboole_0(sK2,sK4)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 1.50/0.59  fof(f221,plain,(
% 1.50/0.59    spl14_11 <=> r1_tarski(sK2,sK4)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 1.50/0.59  fof(f460,plain,(
% 1.50/0.59    sK2 = sK4 | r2_xboole_0(sK2,sK4) | ~spl14_11),
% 1.50/0.59    inference(resolution,[],[f223,f63])).
% 1.50/0.59  fof(f223,plain,(
% 1.50/0.59    r1_tarski(sK2,sK4) | ~spl14_11),
% 1.50/0.59    inference(avatar_component_clause,[],[f221])).
% 1.50/0.59  fof(f456,plain,(
% 1.50/0.59    ~spl14_9),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f455])).
% 1.50/0.59  fof(f455,plain,(
% 1.50/0.59    $false | ~spl14_9),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f454])).
% 1.50/0.59  fof(f454,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | ~spl14_9),
% 1.50/0.59    inference(superposition,[],[f50,f432])).
% 1.50/0.59  fof(f432,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | ~spl14_9),
% 1.50/0.59    inference(resolution,[],[f174,f143])).
% 1.50/0.59  fof(f174,plain,(
% 1.50/0.59    ( ! [X10] : (~r2_hidden(X10,sK2)) ) | ~spl14_9),
% 1.50/0.59    inference(avatar_component_clause,[],[f173])).
% 1.50/0.59  fof(f173,plain,(
% 1.50/0.59    spl14_9 <=> ! [X10] : ~r2_hidden(X10,sK2)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 1.50/0.59  fof(f410,plain,(
% 1.50/0.59    ~spl14_19),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f409])).
% 1.50/0.59  fof(f409,plain,(
% 1.50/0.59    $false | ~spl14_19),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f408])).
% 1.50/0.59  fof(f408,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | ~spl14_19),
% 1.50/0.59    inference(superposition,[],[f49,f389])).
% 1.50/0.59  fof(f389,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | ~spl14_19),
% 1.50/0.59    inference(avatar_component_clause,[],[f387])).
% 1.50/0.59  fof(f387,plain,(
% 1.50/0.59    spl14_19 <=> k1_xboole_0 = sK1),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).
% 1.50/0.59  fof(f49,plain,(
% 1.50/0.59    k1_xboole_0 != sK1),
% 1.50/0.59    inference(cnf_transformation,[],[f22])).
% 1.50/0.59  fof(f403,plain,(
% 1.50/0.59    ~spl14_18),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f402])).
% 1.50/0.59  fof(f402,plain,(
% 1.50/0.59    $false | ~spl14_18),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f401])).
% 1.50/0.59  fof(f401,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | ~spl14_18),
% 1.50/0.59    inference(superposition,[],[f50,f385])).
% 1.50/0.59  fof(f385,plain,(
% 1.50/0.59    k1_xboole_0 = sK2 | ~spl14_18),
% 1.50/0.59    inference(avatar_component_clause,[],[f383])).
% 1.50/0.59  fof(f383,plain,(
% 1.50/0.59    spl14_18 <=> k1_xboole_0 = sK2),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).
% 1.50/0.59  fof(f390,plain,(
% 1.50/0.59    spl14_18 | spl14_19 | ~spl14_15),
% 1.50/0.59    inference(avatar_split_clause,[],[f379,f299,f387,f383])).
% 1.50/0.59  fof(f299,plain,(
% 1.50/0.59    spl14_15 <=> ! [X5] : ~r2_hidden(X5,sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).
% 1.50/0.59  fof(f379,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl14_15),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f375])).
% 1.50/0.59  fof(f375,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl14_15),
% 1.50/0.59    inference(superposition,[],[f64,f362])).
% 1.50/0.59  fof(f362,plain,(
% 1.50/0.59    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | ~spl14_15),
% 1.50/0.59    inference(forward_demodulation,[],[f347,f84])).
% 1.50/0.59  fof(f84,plain,(
% 1.50/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.50/0.59    inference(equality_resolution,[],[f65])).
% 1.50/0.59  fof(f65,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f36])).
% 1.50/0.59  fof(f36,plain,(
% 1.50/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.59    inference(flattening,[],[f35])).
% 1.50/0.59  fof(f35,plain,(
% 1.50/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f10])).
% 1.50/0.59  fof(f10,axiom,(
% 1.50/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.59  fof(f347,plain,(
% 1.50/0.59    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k1_xboole_0,sK4) | ~spl14_15),
% 1.50/0.59    inference(backward_demodulation,[],[f48,f341])).
% 1.50/0.59  fof(f341,plain,(
% 1.50/0.59    k1_xboole_0 = sK3 | ~spl14_15),
% 1.50/0.59    inference(resolution,[],[f300,f143])).
% 1.50/0.59  fof(f300,plain,(
% 1.50/0.59    ( ! [X5] : (~r2_hidden(X5,sK3)) ) | ~spl14_15),
% 1.50/0.59    inference(avatar_component_clause,[],[f299])).
% 1.50/0.59  fof(f48,plain,(
% 1.50/0.59    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.50/0.59    inference(cnf_transformation,[],[f22])).
% 1.50/0.59  fof(f64,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.50/0.59    inference(cnf_transformation,[],[f36])).
% 1.50/0.59  fof(f346,plain,(
% 1.50/0.59    spl14_9 | spl14_8),
% 1.50/0.59    inference(avatar_split_clause,[],[f292,f170,f173])).
% 1.50/0.59  fof(f170,plain,(
% 1.50/0.59    spl14_8 <=> ! [X11] : (~r2_hidden(X11,sK1) | r2_hidden(X11,sK3))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 1.50/0.59  fof(f292,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK1)) )),
% 1.50/0.59    inference(resolution,[],[f110,f81])).
% 1.50/0.59  fof(f81,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f47])).
% 1.50/0.59  fof(f47,plain,(
% 1.50/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.50/0.59    inference(flattening,[],[f46])).
% 1.50/0.59  fof(f46,plain,(
% 1.50/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.50/0.59    inference(nnf_transformation,[],[f9])).
% 1.50/0.59  fof(f9,axiom,(
% 1.50/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.50/0.59  fof(f110,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | r2_hidden(X0,sK3)) )),
% 1.50/0.59    inference(superposition,[],[f79,f48])).
% 1.50/0.59  fof(f79,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f47])).
% 1.50/0.59  fof(f334,plain,(
% 1.50/0.59    ~spl14_10 | ~spl14_14),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f332])).
% 1.50/0.59  fof(f332,plain,(
% 1.50/0.59    $false | (~spl14_10 | ~spl14_14)),
% 1.50/0.59    inference(resolution,[],[f331,f225])).
% 1.50/0.59  fof(f225,plain,(
% 1.50/0.59    r2_hidden(sK8(sK2,sK4),sK4) | ~spl14_10),
% 1.50/0.59    inference(resolution,[],[f219,f67])).
% 1.50/0.59  fof(f219,plain,(
% 1.50/0.59    r2_xboole_0(sK2,sK4) | ~spl14_10),
% 1.50/0.59    inference(avatar_component_clause,[],[f217])).
% 1.50/0.59  fof(f331,plain,(
% 1.50/0.59    ~r2_hidden(sK8(sK2,sK4),sK4) | (~spl14_10 | ~spl14_14)),
% 1.50/0.59    inference(resolution,[],[f324,f219])).
% 1.50/0.59  fof(f324,plain,(
% 1.50/0.59    ( ! [X3] : (~r2_xboole_0(sK2,X3) | ~r2_hidden(sK8(sK2,X3),sK4)) ) | ~spl14_14),
% 1.50/0.59    inference(resolution,[],[f276,f68])).
% 1.50/0.59  fof(f276,plain,(
% 1.50/0.59    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK4)) ) | ~spl14_14),
% 1.50/0.59    inference(avatar_component_clause,[],[f275])).
% 1.50/0.59  fof(f275,plain,(
% 1.50/0.59    spl14_14 <=> ! [X3] : (~r2_hidden(X3,sK4) | r2_hidden(X3,sK2))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).
% 1.50/0.59  fof(f308,plain,(
% 1.50/0.59    spl14_16 | spl14_17),
% 1.50/0.59    inference(avatar_split_clause,[],[f297,f306,f303])).
% 1.50/0.59  fof(f297,plain,(
% 1.50/0.59    ( ! [X6,X7] : (~r2_hidden(X6,sK4) | ~r2_hidden(X7,sK3) | r2_hidden(X7,sK1)) )),
% 1.50/0.59    inference(resolution,[],[f159,f79])).
% 1.50/0.59  fof(f159,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,sK3)) )),
% 1.50/0.59    inference(superposition,[],[f81,f48])).
% 1.50/0.59  fof(f301,plain,(
% 1.50/0.59    spl14_15 | spl14_14),
% 1.50/0.59    inference(avatar_split_clause,[],[f296,f275,f299])).
% 1.50/0.59  fof(f296,plain,(
% 1.50/0.59    ( ! [X4,X5] : (~r2_hidden(X4,sK4) | ~r2_hidden(X5,sK3) | r2_hidden(X4,sK2)) )),
% 1.50/0.59    inference(resolution,[],[f159,f80])).
% 1.50/0.59  fof(f80,plain,(
% 1.50/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f47])).
% 1.50/0.59  fof(f248,plain,(
% 1.50/0.59    spl14_12 | spl14_1 | ~spl14_13),
% 1.50/0.59    inference(avatar_split_clause,[],[f246,f242,f88,f238])).
% 1.50/0.59  fof(f88,plain,(
% 1.50/0.59    spl14_1 <=> sK1 = sK3),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.50/0.59  fof(f242,plain,(
% 1.50/0.59    spl14_13 <=> r1_tarski(sK1,sK3)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).
% 1.50/0.59  fof(f246,plain,(
% 1.50/0.59    sK1 = sK3 | r2_xboole_0(sK1,sK3) | ~spl14_13),
% 1.50/0.59    inference(resolution,[],[f244,f63])).
% 1.50/0.59  fof(f244,plain,(
% 1.50/0.59    r1_tarski(sK1,sK3) | ~spl14_13),
% 1.50/0.59    inference(avatar_component_clause,[],[f242])).
% 1.50/0.59  fof(f245,plain,(
% 1.50/0.59    spl14_1 | spl14_12 | spl14_13 | ~spl14_8),
% 1.50/0.59    inference(avatar_split_clause,[],[f235,f170,f242,f238,f88])).
% 1.50/0.59  fof(f235,plain,(
% 1.50/0.59    r1_tarski(sK1,sK3) | r2_xboole_0(sK1,sK3) | sK1 = sK3 | ~spl14_8),
% 1.50/0.59    inference(resolution,[],[f212,f104])).
% 1.50/0.59  fof(f212,plain,(
% 1.50/0.59    ( ! [X0] : (~r2_hidden(sK7(X0,sK3),sK1) | r1_tarski(X0,sK3)) ) | ~spl14_8),
% 1.50/0.59    inference(resolution,[],[f171,f60])).
% 1.50/0.59  fof(f60,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f32])).
% 1.50/0.59  fof(f171,plain,(
% 1.50/0.59    ( ! [X11] : (r2_hidden(X11,sK3) | ~r2_hidden(X11,sK1)) ) | ~spl14_8),
% 1.50/0.59    inference(avatar_component_clause,[],[f170])).
% 1.50/0.59  fof(f224,plain,(
% 1.50/0.59    spl14_2 | spl14_10 | spl14_11 | ~spl14_7),
% 1.50/0.59    inference(avatar_split_clause,[],[f214,f166,f221,f217,f92])).
% 1.50/0.59  fof(f166,plain,(
% 1.50/0.59    spl14_7 <=> ! [X8] : (~r2_hidden(X8,sK2) | r2_hidden(X8,sK4))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 1.50/0.59  fof(f214,plain,(
% 1.50/0.59    r1_tarski(sK2,sK4) | r2_xboole_0(sK2,sK4) | sK2 = sK4 | ~spl14_7),
% 1.50/0.59    inference(resolution,[],[f210,f104])).
% 1.50/0.59  fof(f210,plain,(
% 1.50/0.59    ( ! [X0] : (~r2_hidden(sK7(X0,sK4),sK2) | r1_tarski(X0,sK4)) ) | ~spl14_7),
% 1.50/0.59    inference(resolution,[],[f167,f60])).
% 1.50/0.59  fof(f167,plain,(
% 1.50/0.59    ( ! [X8] : (r2_hidden(X8,sK4) | ~r2_hidden(X8,sK2)) ) | ~spl14_7),
% 1.50/0.59    inference(avatar_component_clause,[],[f166])).
% 1.50/0.59  fof(f203,plain,(
% 1.50/0.59    ~spl14_6),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f202])).
% 1.50/0.59  fof(f202,plain,(
% 1.50/0.59    $false | ~spl14_6),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f201])).
% 1.50/0.59  fof(f201,plain,(
% 1.50/0.59    k1_xboole_0 != k1_xboole_0 | ~spl14_6),
% 1.50/0.59    inference(superposition,[],[f49,f179])).
% 1.50/0.59  fof(f179,plain,(
% 1.50/0.59    k1_xboole_0 = sK1 | ~spl14_6),
% 1.50/0.59    inference(resolution,[],[f164,f143])).
% 1.50/0.59  fof(f164,plain,(
% 1.50/0.59    ( ! [X9] : (~r2_hidden(X9,sK1)) ) | ~spl14_6),
% 1.50/0.59    inference(avatar_component_clause,[],[f163])).
% 1.50/0.59  fof(f163,plain,(
% 1.50/0.59    spl14_6 <=> ! [X9] : ~r2_hidden(X9,sK1)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 1.50/0.59  fof(f168,plain,(
% 1.50/0.59    spl14_6 | spl14_7),
% 1.50/0.59    inference(avatar_split_clause,[],[f157,f166,f163])).
% 1.50/0.59  fof(f157,plain,(
% 1.50/0.59    ( ! [X8,X9] : (~r2_hidden(X8,sK2) | ~r2_hidden(X9,sK1) | r2_hidden(X8,sK4)) )),
% 1.50/0.59    inference(resolution,[],[f81,f113])).
% 1.50/0.59  fof(f113,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK2)) | r2_hidden(X1,sK4)) )),
% 1.50/0.59    inference(superposition,[],[f80,f48])).
% 1.50/0.59  fof(f95,plain,(
% 1.50/0.59    ~spl14_1 | ~spl14_2),
% 1.50/0.59    inference(avatar_split_clause,[],[f51,f92,f88])).
% 1.50/0.59  fof(f51,plain,(
% 1.50/0.59    sK2 != sK4 | sK1 != sK3),
% 1.50/0.59    inference(cnf_transformation,[],[f22])).
% 1.50/0.59  % SZS output end Proof for theBenchmark
% 1.50/0.59  % (17880)------------------------------
% 1.50/0.59  % (17880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.59  % (17880)Termination reason: Refutation
% 1.50/0.59  
% 1.50/0.59  % (17880)Memory used [KB]: 6396
% 1.50/0.59  % (17880)Time elapsed: 0.159 s
% 1.50/0.59  % (17880)------------------------------
% 1.50/0.59  % (17880)------------------------------
% 1.50/0.59  % (17864)Success in time 0.228 s
%------------------------------------------------------------------------------
