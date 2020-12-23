%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t70_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 229 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :    7
%              Number of atoms          :  242 ( 547 expanded)
%              Number of equality atoms :   59 ( 167 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f64,f71,f72,f80,f95,f96,f103,f112,f120,f142,f143,f144,f155,f162,f164,f175,f177,f178,f179,f181,f183,f207])).

fof(f207,plain,
    ( ~ spl3_0
    | spl3_7
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f205,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_9
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f205,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_0
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f204,f63])).

fof(f63,plain,
    ( sK0 != sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_7
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f204,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | ~ spl3_0 ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | sK0 = sK1
    | r2_hidden(sK1,sK2)
    | ~ spl3_0 ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_0
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      | X0 = X1
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t70_zfmisc_1.p',l38_zfmisc_1)).

fof(f183,plain,
    ( spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f182,f69,f101])).

fof(f101,plain,
    ( spl3_12
  <=> k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f182,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f181,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f180,f48,f53])).

fof(f53,plain,
    ( spl3_4
  <=> k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f48,plain,
    ( spl3_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f180,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f179,plain,
    ( ~ spl3_9
    | ~ spl3_23
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f165,f42,f173,f69])).

fof(f173,plain,
    ( spl3_23
  <=> k1_tarski(sK0) != k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f165,plain,
    ( k1_tarski(sK0) != k1_tarski(sK1)
    | ~ r2_hidden(sK1,sK2)
    | ~ spl3_0 ),
    inference(superposition,[],[f81,f43])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X1,X0),X2) != k1_tarski(X0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t70_zfmisc_1.p',commutativity_k2_tarski)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,
    ( ~ spl3_3
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f167,f42,f48])).

fof(f167,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_0 ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_0 ),
    inference(superposition,[],[f31,f43])).

fof(f177,plain,
    ( ~ spl3_0
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f46,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f175,plain,
    ( ~ spl3_23
    | ~ spl3_0
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f168,f66,f42,f173])).

fof(f66,plain,
    ( spl3_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f168,plain,
    ( k1_tarski(sK0) != k1_tarski(sK1)
    | ~ spl3_0
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f165,f67])).

fof(f67,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f164,plain,
    ( spl3_18
    | spl3_21 ),
    inference(avatar_split_clause,[],[f163,f160,f153])).

fof(f153,plain,
    ( spl3_18
  <=> k4_xboole_0(k2_tarski(sK2,sK2),sK0) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f160,plain,
    ( spl3_21
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f163,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK2),sK0) = k1_tarski(sK2)
    | ~ spl3_21 ),
    inference(resolution,[],[f161,f37])).

fof(f161,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( ~ spl3_21
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f147,f45,f160])).

fof(f147,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t70_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f155,plain,
    ( spl3_18
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f146,f45,f153])).

fof(f146,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK2),sK0) = k1_tarski(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_tarski(X0) ) ),
    inference(resolution,[],[f37,f27])).

fof(f144,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f122,f53,f48])).

fof(f122,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f121])).

fof(f121,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f54])).

fof(f54,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f143,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f131,f53,f48])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f81,f54])).

fof(f142,plain,
    ( spl3_1
    | spl3_3
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f40,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f135,f49])).

fof(f135,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK2)
        | k4_xboole_0(k2_tarski(X3,sK1),sK2) = k1_tarski(X3) )
    | ~ spl3_8 ),
    inference(resolution,[],[f28,f67])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,
    ( spl3_16
    | spl3_15 ),
    inference(avatar_split_clause,[],[f113,f110,f118])).

fof(f118,plain,
    ( spl3_16
  <=> k4_xboole_0(k2_tarski(sK2,sK2),sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f110,plain,
    ( spl3_15
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f113,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK2),sK1) = k1_tarski(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f111,f37])).

fof(f111,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl3_15
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f104,f66,f110])).

fof(f104,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f67,f27])).

fof(f103,plain,
    ( spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f93,f69,f101])).

fof(f93,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK1),sK2) = k1_tarski(sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f37,f70])).

fof(f96,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f90,f48,f53])).

fof(f90,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k1_tarski(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f37,f49])).

fof(f95,plain,
    ( spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f57,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_5
  <=> k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( ~ spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f73,f66,f78])).

fof(f78,plain,
    ( spl3_11
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f26,f67])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t70_zfmisc_1.p',t7_boole)).

fof(f72,plain,
    ( spl3_0
    | spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f22,f66,f59,f42])).

fof(f59,plain,
    ( spl3_6
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f22,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK1
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t70_zfmisc_1.p',t70_zfmisc_1)).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_9
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f45,f69,f39])).

fof(f23,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f45,f62,f56])).

fof(f51,plain,
    ( r2_hidden(sK0,sK2)
    | sK0 != sK1
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k1_tarski(sK0) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( r2_hidden(sK0,sK2)
    | sK0 != sK1
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,
    ( spl3_0
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f48,f42])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
