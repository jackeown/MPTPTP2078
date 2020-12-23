%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t115_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 204 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  255 ( 501 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f41,f48,f69,f74,f88,f92,f98,f99,f112,f117,f118,f123,f125,f135,f140,f141,f147,f148,f151,f160,f162])).

fof(f162,plain,
    ( ~ spl3_10
    | spl3_13
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f157,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_13
  <=> ~ r2_hidden(sK2(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f157,plain,
    ( r2_hidden(sK2(sK1,sK0),sK0)
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(resolution,[],[f134,f78])).

fof(f78,plain,
    ( r2_hidden(sK2(sK1,sK0),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_10
  <=> r2_hidden(sK2(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f134,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(X4,sK0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_20
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f160,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f62,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_7
  <=> ~ r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f156,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(resolution,[],[f134,f65])).

fof(f65,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_8
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f151,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f149,f64,f32,f61])).

fof(f32,plain,
    ( spl3_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f126,f33])).

fof(f33,plain,
    ( sK0 != sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f126,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | sK0 = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t115_zfmisc_1.p',t2_tarski)).

fof(f148,plain,
    ( ~ spl3_8
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(resolution,[],[f142,f65])).

fof(f142,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f134,f111])).

fof(f111,plain,
    ( ! [X8] : ~ r2_hidden(X8,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_16
  <=> ! [X8] : ~ r2_hidden(X8,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f147,plain,
    ( ~ spl3_10
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(resolution,[],[f142,f78])).

fof(f141,plain,
    ( ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(resolution,[],[f131,f65])).

fof(f131,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_18
  <=> ! [X5] : ~ r2_hidden(X5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f140,plain,
    ( ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(resolution,[],[f131,f78])).

fof(f135,plain,
    ( spl3_18
    | spl3_20
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f104,f39,f133,f130])).

fof(f39,plain,
    ( spl3_2
  <=> k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | r2_hidden(X4,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t115_zfmisc_1.p',l54_zfmisc_1)).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f27,f40])).

fof(f40,plain,
    ( k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f125,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f120,f84])).

fof(f84,plain,
    ( r2_hidden(sK2(sK1,sK0),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_12
  <=> r2_hidden(sK2(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f120,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),sK0)
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(resolution,[],[f108,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_11
  <=> ~ r2_hidden(sK2(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f108,plain,
    ( ! [X9] :
        ( r2_hidden(X9,sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_14
  <=> ! [X9] :
        ( ~ r2_hidden(X9,sK0)
        | r2_hidden(X9,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f123,plain,
    ( ~ spl3_6
    | spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f119,f59])).

fof(f59,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_6
  <=> r2_hidden(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f119,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_9
  <=> ~ r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f118,plain,
    ( ~ spl3_6
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(resolution,[],[f111,f59])).

fof(f117,plain,
    ( ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(resolution,[],[f111,f84])).

fof(f112,plain,
    ( spl3_14
    | spl3_16
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f39,f110,f107])).

fof(f96,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(X8,sK0)
        | ~ r2_hidden(X9,sK0)
        | r2_hidden(X9,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f25,f40])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( spl3_12
    | spl3_1
    | spl3_11 ),
    inference(avatar_split_clause,[],[f93,f80,f32,f83])).

fof(f93,plain,
    ( r2_hidden(sK2(sK1,sK0),sK0)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f89,f33])).

fof(f89,plain,
    ( r2_hidden(sK2(sK1,sK0),sK0)
    | sK0 = sK1
    | ~ spl3_11 ),
    inference(resolution,[],[f81,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,
    ( spl3_6
    | spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f75,f67,f32,f58])).

fof(f75,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f71,plain,
    ( r2_hidden(sK2(sK0,sK1),sK0)
    | sK0 = sK1
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f21])).

fof(f92,plain,
    ( spl3_1
    | spl3_11
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f90,f33])).

fof(f90,plain,
    ( sK0 = sK1
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f89,f87])).

fof(f88,plain,
    ( ~ spl3_11
    | ~ spl3_13
    | spl3_1 ),
    inference(avatar_split_clause,[],[f53,f32,f86,f80])).

fof(f53,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),sK0)
    | ~ r2_hidden(sK2(sK1,sK0),sK1)
    | ~ spl3_1 ),
    inference(extensionality_resolution,[],[f22,f33])).

fof(f74,plain,
    ( spl3_1
    | spl3_7
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,
    ( sK0 = sK1
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f69,plain,
    ( ~ spl3_7
    | ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f52,f32,f67,f61])).

fof(f52,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ r2_hidden(sK2(sK0,sK1),sK0)
    | ~ spl3_1 ),
    inference(extensionality_resolution,[],[f22,f33])).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f46,plain,
    ( spl3_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t115_zfmisc_1.p',d2_xboole_0)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t115_zfmisc_1.p',t115_zfmisc_1)).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
