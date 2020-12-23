%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t43_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:07 EDT 2019

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 187 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 465 expanded)
%              Number of equality atoms :   75 ( 222 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f58,f71,f72,f79,f89,f101,f112,f113,f125,f133,f140,f150,f152,f157,f167,f185,f189])).

fof(f189,plain,
    ( spl3_3
    | ~ spl3_4
    | spl3_15
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f187,f51])).

fof(f51,plain,
    ( k1_xboole_0 != sK2
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f187,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f186,f111])).

fof(f111,plain,
    ( sK1 != sK2
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_15
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f186,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(resolution,[],[f184,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f158,f54])).

fof(f54,plain,
    ( k1_tarski(sK0) = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_4
  <=> k1_tarski(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_tarski(sK0) = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(superposition,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',l3_zfmisc_1)).

fof(f184,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_22
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f185,plain,
    ( spl3_22
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f177,f123,f183])).

fof(f123,plain,
    ( spl3_16
  <=> k2_xboole_0(sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f177,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f93,f124])).

fof(f124,plain,
    ( k2_xboole_0(sK1,sK2) = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f93,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',t7_xboole_1)).

fof(f167,plain,
    ( spl3_8
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f98,f87,f53,f66])).

fof(f66,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( spl3_12
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f98,plain,
    ( k1_tarski(sK0) = sK1
    | k1_xboole_0 = sK1
    | ~ spl3_12 ),
    inference(resolution,[],[f26,f88])).

fof(f88,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f157,plain,
    ( spl3_4
    | ~ spl3_0
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f154,f123,f43,f53])).

fof(f43,plain,
    ( spl3_0
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f154,plain,
    ( k1_tarski(sK0) = sK1
    | ~ spl3_0
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f124,f44])).

fof(f44,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f43])).

fof(f152,plain,
    ( ~ spl3_8
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f35,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',t1_boole)).

fof(f147,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f67,f136])).

fof(f136,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_21
  <=> ~ r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f150,plain,
    ( ~ spl3_0
    | spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f148,f64])).

fof(f64,plain,
    ( k1_tarski(sK0) != sK2
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_7
  <=> k1_tarski(sK0) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f148,plain,
    ( k1_tarski(sK0) = sK2
    | ~ spl3_0
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f141,f90])).

fof(f90,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f33,f30])).

fof(f141,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_0
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f67,f44])).

fof(f140,plain,
    ( spl3_20
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f116,f53,f138])).

fof(f138,plain,
    ( spl3_20
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f116,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f38,f54])).

fof(f38,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,
    ( ~ spl3_19
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f117,f53,f131])).

fof(f131,plain,
    ( spl3_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f117,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f36,f54])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',fc2_xboole_0)).

fof(f125,plain,
    ( spl3_16
    | ~ spl3_0
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f105,f87,f69,f43,f123])).

fof(f69,plain,
    ( spl3_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f105,plain,
    ( k2_xboole_0(sK1,sK2) = sK1
    | ~ spl3_0
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f102,f44])).

fof(f102,plain,
    ( k1_tarski(sK0) = sK1
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f98,f70])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f113,plain,
    ( spl3_4
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f87,f69,f53])).

fof(f112,plain,
    ( ~ spl3_15
    | spl3_7
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f104,f87,f69,f63,f110])).

fof(f104,plain,
    ( sK1 != sK2
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f102,f64])).

fof(f101,plain,
    ( spl3_5
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f99,f70])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f57,plain,
    ( k1_tarski(sK0) != sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_5
  <=> k1_tarski(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( spl3_12
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f80,f43,f87])).

fof(f80,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_0 ),
    inference(superposition,[],[f35,f44])).

fof(f79,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f77,plain,
    ( spl3_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',d2_xboole_0)).

fof(f72,plain,
    ( ~ spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f24,f56,f63])).

fof(f24,plain,
    ( k1_tarski(sK0) != sK1
    | k1_tarski(sK0) != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t43_zfmisc_1.p',t43_zfmisc_1)).

fof(f71,plain,
    ( ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f23,f69,f63])).

fof(f23,plain,
    ( k1_xboole_0 != sK1
    | k1_tarski(sK0) != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f22,f56,f50])).

fof(f22,plain,
    ( k1_tarski(sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
