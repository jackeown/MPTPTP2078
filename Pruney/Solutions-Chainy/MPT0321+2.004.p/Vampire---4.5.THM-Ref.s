%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:28 EST 2020

% Result     : Theorem 9.44s
% Output     : Refutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 662 expanded)
%              Number of leaves         :   52 ( 271 expanded)
%              Depth                    :   15
%              Number of atoms          :  743 (1488 expanded)
%              Number of equality atoms :  212 ( 612 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f71,f75,f98,f111,f128,f143,f152,f156,f171,f271,f290,f319,f781,f818,f889,f1160,f1327,f1713,f2227,f5332,f5427,f5831,f6160,f6183,f6491,f6683,f6821,f6850,f7680,f7832,f7899,f8899,f16298,f16462,f16567,f16643])).

fof(f16643,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_166
    | spl4_191
    | ~ spl4_221 ),
    inference(avatar_contradiction_clause,[],[f16642])).

fof(f16642,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_166
    | spl4_191
    | ~ spl4_221 ),
    inference(subsumption_resolution,[],[f16641,f8898])).

fof(f8898,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_191 ),
    inference(avatar_component_clause,[],[f8897])).

fof(f8897,plain,
    ( spl4_191
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).

fof(f16641,plain,
    ( r1_tarski(sK0,sK2)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_166
    | ~ spl4_221 ),
    inference(forward_demodulation,[],[f16640,f7679])).

fof(f7679,plain,
    ( sK0 = k2_xboole_0(sK0,sK2)
    | ~ spl4_166 ),
    inference(avatar_component_clause,[],[f7678])).

fof(f7678,plain,
    ( spl4_166
  <=> sK0 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f16640,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_221 ),
    inference(subsumption_resolution,[],[f16639,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f16639,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_221 ),
    inference(forward_demodulation,[],[f16638,f74])).

fof(f74,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_5
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f16638,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | spl4_2
    | ~ spl4_26
    | ~ spl4_154
    | ~ spl4_221 ),
    inference(forward_demodulation,[],[f16539,f6849])).

fof(f6849,plain,
    ( sK3 = k2_xboole_0(sK1,sK3)
    | ~ spl4_154 ),
    inference(avatar_component_clause,[],[f6848])).

fof(f6848,plain,
    ( spl4_154
  <=> sK3 = k2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f16539,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_xboole_0(sK0,sK2),sK2)
    | spl4_2
    | ~ spl4_26
    | ~ spl4_221 ),
    inference(superposition,[],[f491,f16461])).

fof(f16461,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl4_221 ),
    inference(avatar_component_clause,[],[f16460])).

fof(f16460,plain,
    ( spl4_221
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).

fof(f491,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK1))
        | r1_tarski(k2_xboole_0(sK0,sK2),X0) )
    | spl4_2
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f482,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK1))
        | k1_xboole_0 = sK1
        | r1_tarski(k2_xboole_0(sK0,sK2),X0) )
    | ~ spl4_26 ),
    inference(superposition,[],[f30,f318])).

fof(f318,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl4_26
  <=> k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f16567,plain,
    ( ~ spl4_17
    | spl4_151
    | ~ spl4_221 ),
    inference(avatar_contradiction_clause,[],[f16566])).

fof(f16566,plain,
    ( $false
    | ~ spl4_17
    | spl4_151
    | ~ spl4_221 ),
    inference(subsumption_resolution,[],[f16565,f6490])).

fof(f6490,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl4_151 ),
    inference(avatar_component_clause,[],[f6489])).

fof(f6489,plain,
    ( spl4_151
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).

fof(f16565,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl4_17
    | ~ spl4_221 ),
    inference(subsumption_resolution,[],[f16497,f56])).

fof(f16497,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,sK1)
    | ~ spl4_17
    | ~ spl4_221 ),
    inference(superposition,[],[f155,f16461])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))
        | r1_tarski(sK3,X2) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_17
  <=> ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))
        | r1_tarski(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f16462,plain,
    ( spl4_221
    | ~ spl4_5
    | ~ spl4_154
    | ~ spl4_218 ),
    inference(avatar_split_clause,[],[f16372,f16296,f6848,f73,f16460])).

fof(f16296,plain,
    ( spl4_218
  <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).

fof(f16372,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ spl4_5
    | ~ spl4_154
    | ~ spl4_218 ),
    inference(subsumption_resolution,[],[f7551,f16371])).

fof(f16371,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_154
    | ~ spl4_218 ),
    inference(forward_demodulation,[],[f16370,f74])).

fof(f16370,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_154
    | ~ spl4_218 ),
    inference(forward_demodulation,[],[f16369,f6849])).

fof(f16369,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_218 ),
    inference(trivial_inequality_removal,[],[f16361])).

fof(f16361,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_218 ),
    inference(superposition,[],[f2983,f16297])).

fof(f16297,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_218 ),
    inference(avatar_component_clause,[],[f16296])).

fof(f2983,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
        | r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)),k2_zfmisc_1(sK2,X0)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f581])).

fof(f581,plain,
    ( ! [X3] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k4_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)),k2_zfmisc_1(sK2,X3))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f246])).

fof(f246,plain,
    ( ! [X1] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f84,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f84,plain,
    ( ! [X7] : k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f41,f74])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f7551,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_154 ),
    inference(forward_demodulation,[],[f7550,f74])).

fof(f7550,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK1)
    | ~ spl4_5
    | ~ spl4_154 ),
    inference(forward_demodulation,[],[f7492,f74])).

fof(f7492,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1))
    | k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK1)
    | ~ spl4_5
    | ~ spl4_154 ),
    inference(superposition,[],[f261,f6849])).

fof(f261,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3)),k2_zfmisc_1(sK2,X2))
        | k2_zfmisc_1(sK2,X2) = k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f253,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f253,plain,
    ( ! [X3] : r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f84])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f16298,plain,
    ( spl4_218
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_55
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(avatar_split_clause,[],[f16253,f7897,f7830,f1158,f816,f73,f16296])).

fof(f816,plain,
    ( spl4_43
  <=> sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1158,plain,
    ( spl4_55
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f7830,plain,
    ( spl4_170
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f7897,plain,
    ( spl4_174
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f16253,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_55
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16252,f74])).

fof(f16252,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_55
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16251,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f16251,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_55
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16250,f1159])).

fof(f1159,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f16250,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16249,f54])).

fof(f54,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f16249,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_170
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16248,f7831])).

fof(f7831,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_170 ),
    inference(avatar_component_clause,[],[f7830])).

fof(f16248,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl4_5
    | ~ spl4_43
    | ~ spl4_174 ),
    inference(forward_demodulation,[],[f16234,f8257])).

fof(f8257,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),sK1) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
    | ~ spl4_174 ),
    inference(superposition,[],[f39,f7898])).

fof(f7898,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_174 ),
    inference(avatar_component_clause,[],[f7897])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f16234,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl4_5
    | ~ spl4_43 ),
    inference(superposition,[],[f4644,f817])).

fof(f817,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f816])).

fof(f4644,plain,
    ( ! [X1] : k3_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f48,f636])).

fof(f636,plain,
    ( ! [X1] : k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f633,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f633,plain,
    ( ! [X1] : k3_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(superposition,[],[f48,f205])).

fof(f205,plain,
    ( ! [X2] : k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X2,sK2),sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f82])).

fof(f82,plain,
    ( ! [X5] : k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f40,f74])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f8899,plain,
    ( spl4_4
    | ~ spl4_191
    | ~ spl4_149 ),
    inference(avatar_split_clause,[],[f6262,f6158,f8897,f69])).

fof(f69,plain,
    ( spl4_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f6158,plain,
    ( spl4_149
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_149])])).

fof(f6262,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_149 ),
    inference(resolution,[],[f6159,f44])).

fof(f6159,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_149 ),
    inference(avatar_component_clause,[],[f6158])).

fof(f7899,plain,
    ( spl4_174
    | ~ spl4_83
    | ~ spl4_154 ),
    inference(avatar_split_clause,[],[f7510,f6848,f1711,f7897])).

fof(f1711,plain,
    ( spl4_83
  <=> ! [X0] : r1_tarski(X0,k2_xboole_0(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f7510,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_83
    | ~ spl4_154 ),
    inference(superposition,[],[f1754,f6849])).

fof(f1754,plain,
    ( ! [X1] : k3_xboole_0(X1,k2_xboole_0(X1,sK3)) = X1
    | ~ spl4_83 ),
    inference(forward_demodulation,[],[f1752,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1752,plain,
    ( ! [X1] : k3_xboole_0(X1,k2_xboole_0(X1,sK3)) = k4_xboole_0(X1,k1_xboole_0)
    | ~ spl4_83 ),
    inference(superposition,[],[f48,f1731])).

fof(f1731,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,sK3))
    | ~ spl4_83 ),
    inference(superposition,[],[f1721,f52])).

fof(f1721,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK3,X2))
    | ~ spl4_83 ),
    inference(resolution,[],[f1712,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1712,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK3,X0))
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f1711])).

fof(f7832,plain,
    ( spl4_170
    | ~ spl4_153 ),
    inference(avatar_split_clause,[],[f7432,f6819,f7830])).

fof(f6819,plain,
    ( spl4_153
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).

fof(f7432,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_153 ),
    inference(forward_demodulation,[],[f7431,f37])).

fof(f7431,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK0,sK2)
    | ~ spl4_153 ),
    inference(forward_demodulation,[],[f7429,f51])).

fof(f7429,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,sK0)
    | ~ spl4_153 ),
    inference(superposition,[],[f48,f6820])).

fof(f6820,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl4_153 ),
    inference(avatar_component_clause,[],[f6819])).

fof(f7680,plain,
    ( spl4_166
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f7322,f6681,f7678])).

fof(f6681,plain,
    ( spl4_152
  <=> sK0 = k2_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f7322,plain,
    ( sK0 = k2_xboole_0(sK0,sK2)
    | ~ spl4_152 ),
    inference(superposition,[],[f6682,f52])).

fof(f6682,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_152 ),
    inference(avatar_component_clause,[],[f6681])).

fof(f6850,plain,
    ( spl4_154
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f6321,f6181,f6848])).

fof(f6181,plain,
    ( spl4_150
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f6321,plain,
    ( sK3 = k2_xboole_0(sK1,sK3)
    | ~ spl4_150 ),
    inference(resolution,[],[f6182,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f6182,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f6181])).

fof(f6821,plain,
    ( spl4_153
    | ~ spl4_149 ),
    inference(avatar_split_clause,[],[f6263,f6158,f6819])).

fof(f6263,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl4_149 ),
    inference(resolution,[],[f6159,f32])).

fof(f6683,plain,
    ( spl4_152
    | ~ spl4_149 ),
    inference(avatar_split_clause,[],[f6261,f6158,f6681])).

fof(f6261,plain,
    ( sK0 = k2_xboole_0(sK2,sK0)
    | ~ spl4_149 ),
    inference(resolution,[],[f6159,f45])).

fof(f6491,plain,
    ( ~ spl4_151
    | spl4_3
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f6324,f6181,f66,f6489])).

fof(f66,plain,
    ( spl4_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f6324,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl4_3
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f6322,f67])).

fof(f67,plain,
    ( sK1 != sK3
    | spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f6322,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3
    | ~ spl4_150 ),
    inference(resolution,[],[f6182,f44])).

fof(f6183,plain,
    ( spl4_150
    | spl4_1
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f5981,f5829,f58,f6181])).

fof(f58,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f5829,plain,
    ( spl4_148
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f5981,plain,
    ( r1_tarski(sK1,sK3)
    | spl4_1
    | ~ spl4_148 ),
    inference(subsumption_resolution,[],[f5977,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f5977,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK1,sK3)
    | ~ spl4_148 ),
    inference(resolution,[],[f5830,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5830,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_148 ),
    inference(avatar_component_clause,[],[f5829])).

fof(f6160,plain,
    ( spl4_149
    | ~ spl4_9
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f5976,f5829,f96,f6158])).

fof(f96,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f5976,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_9
    | ~ spl4_148 ),
    inference(resolution,[],[f5830,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | r1_tarski(sK2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f5831,plain,
    ( spl4_148
    | ~ spl4_94
    | ~ spl4_137 ),
    inference(avatar_split_clause,[],[f5512,f5425,f2225,f5829])).

fof(f2225,plain,
    ( spl4_94
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f5425,plain,
    ( spl4_137
  <=> k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f5512,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_94
    | ~ spl4_137 ),
    inference(superposition,[],[f2226,f5426])).

fof(f5426,plain,
    ( k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl4_137 ),
    inference(avatar_component_clause,[],[f5425])).

fof(f2226,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f2225])).

fof(f5427,plain,
    ( spl4_137
    | ~ spl4_131 ),
    inference(avatar_split_clause,[],[f5378,f5330,f5425])).

fof(f5330,plain,
    ( spl4_131
  <=> k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f5378,plain,
    ( k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))
    | ~ spl4_131 ),
    inference(superposition,[],[f5331,f37])).

fof(f5331,plain,
    ( k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0)
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f5330])).

fof(f5332,plain,
    ( spl4_131
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_22
    | ~ spl4_70
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f4591,f2225,f1325,f288,f154,f96,f73,f5330])).

fof(f288,plain,
    ( spl4_22
  <=> k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1325,plain,
    ( spl4_70
  <=> ! [X0] : r1_tarski(X0,k2_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f4591,plain,
    ( k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_22
    | ~ spl4_70
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f4590,f289])).

fof(f289,plain,
    ( k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f288])).

fof(f4590,plain,
    ( k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_22
    | ~ spl4_70
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f4589,f2371])).

fof(f2371,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))
    | ~ spl4_94 ),
    inference(resolution,[],[f2226,f32])).

fof(f4589,plain,
    ( k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_22
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f4588,f760])).

fof(f760,plain,
    ( ! [X1] : sK3 = k3_xboole_0(sK3,k2_xboole_0(X1,sK3))
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f758,f37])).

fof(f758,plain,
    ( ! [X1] : k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(X1,sK3))
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(superposition,[],[f48,f732])).

fof(f732,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X2,sK3))
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f720,f32])).

fof(f720,plain,
    ( ! [X0] : r1_tarski(sK3,k2_xboole_0(X0,sK3))
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f239,f155])).

fof(f239,plain,
    ( ! [X1] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f226,f52])).

fof(f226,plain,
    ( ! [X3] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f83])).

fof(f83,plain,
    ( ! [X6] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X6)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))
    | ~ spl4_5 ),
    inference(superposition,[],[f41,f74])).

fof(f4588,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k2_xboole_0(sK1,sK3)))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_22
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f4587,f51])).

fof(f4587,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(sK0,k3_xboole_0(k2_xboole_0(sK1,sK3),sK3))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_22
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f4586,f1496])).

fof(f1496,plain,
    ( ! [X8,X7,X9] : k2_zfmisc_1(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(k2_xboole_0(X7,sK2),X9))
    | ~ spl4_70 ),
    inference(superposition,[],[f39,f1360])).

fof(f1360,plain,
    ( ! [X1] : k3_xboole_0(X1,k2_xboole_0(X1,sK2)) = X1
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f1358,f37])).

fof(f1358,plain,
    ( ! [X1] : k3_xboole_0(X1,k2_xboole_0(X1,sK2)) = k4_xboole_0(X1,k1_xboole_0)
    | ~ spl4_70 ),
    inference(superposition,[],[f48,f1340])).

fof(f1340,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,sK2))
    | ~ spl4_70 ),
    inference(superposition,[],[f1330,f52])).

fof(f1330,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK2,X2))
    | ~ spl4_70 ),
    inference(resolution,[],[f1326,f32])).

fof(f1326,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK2,X0))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f4586,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f4529,f282])).

fof(f282,plain,
    ( ! [X0] : k2_xboole_0(X0,sK2) = k2_xboole_0(sK2,k2_xboole_0(X0,sK2))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f272,f45])).

fof(f272,plain,
    ( ! [X0] : r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f194,f97])).

fof(f194,plain,
    ( ! [X1] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f183,f52])).

fof(f183,plain,
    ( ! [X3] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f81])).

fof(f81,plain,
    ( ! [X4] : k2_zfmisc_1(k2_xboole_0(sK2,X4),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f40,f74])).

fof(f4529,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,k2_xboole_0(sK0,sK2)),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(k2_xboole_0(sK2,k2_xboole_0(sK0,sK2)),sK3))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(superposition,[],[f622,f289])).

fof(f622,plain,
    ( ! [X1] : k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f608,f51])).

fof(f608,plain,
    ( ! [X1] : k3_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k2_zfmisc_1(X1,sK3)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)))
    | ~ spl4_5 ),
    inference(superposition,[],[f48,f182])).

fof(f182,plain,
    ( ! [X2] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X2),sK3),k2_zfmisc_1(X2,sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f81])).

fof(f2227,plain,
    ( spl4_94
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f386,f288,f73,f2225])).

fof(f386,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(superposition,[],[f194,f289])).

fof(f1713,plain,
    ( spl4_83
    | spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f736,f73,f86,f1711])).

fof(f86,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f736,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2
        | r1_tarski(X0,k2_xboole_0(sK3,X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f265,f31])).

fof(f265,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f253,f52])).

fof(f1327,plain,
    ( spl4_70
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f687,f73,f89,f1325])).

fof(f89,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f687,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3
        | r1_tarski(X0,k2_xboole_0(sK2,X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f216,f30])).

fof(f216,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f206,f52])).

fof(f206,plain,
    ( ! [X3] : r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f82])).

fof(f1160,plain,
    ( spl4_55
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f917,f779,f269,f73,f1158])).

fof(f269,plain,
    ( spl4_20
  <=> k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f779,plain,
    ( spl4_38
  <=> k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f917,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f916,f780])).

fof(f780,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f779])).

fof(f916,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f893,f270])).

fof(f270,plain,
    ( k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f893,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3))
    | ~ spl4_5 ),
    inference(superposition,[],[f213,f54])).

fof(f213,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f206,f32])).

fof(f889,plain,
    ( spl4_16
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f801,f779,f150])).

fof(f150,plain,
    ( spl4_16
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f801,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_38 ),
    inference(superposition,[],[f47,f780])).

fof(f818,plain,
    ( spl4_43
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f805,f147,f816])).

fof(f147,plain,
    ( spl4_15
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f805,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f148,f45])).

fof(f148,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f781,plain,
    ( spl4_38
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f620,f269,f73,f779])).

fof(f620,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f619,f37])).

fof(f619,plain,
    ( k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f618,f37])).

fof(f618,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f617,f270])).

fof(f617,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3),k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f605,f502])).

fof(f502,plain,
    ( ! [X1] : k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f177,f82])).

fof(f177,plain,
    ( ! [X1] : k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f81,f52])).

fof(f605,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f182,f54])).

fof(f319,plain,
    ( spl4_26
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f231,f73,f317])).

fof(f231,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f222,f52])).

fof(f222,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f83,f40])).

fof(f290,plain,
    ( spl4_22
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f187,f73,f288])).

fof(f187,plain,
    ( k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f176,f52])).

fof(f176,plain,
    ( k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f81,f41])).

fof(f271,plain,
    ( spl4_20
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f185,f73,f269])).

fof(f185,plain,
    ( k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f184,f52])).

fof(f184,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f174,f52])).

fof(f174,plain,
    ( k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f81,f54])).

fof(f171,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f169,f93])).

fof(f93,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_8
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f169,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f167,f54])).

fof(f167,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f74,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f156,plain,
    ( spl4_6
    | spl4_17
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f78,f73,f154,f86])).

fof(f78,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))
        | k1_xboole_0 = sK2
        | r1_tarski(sK3,X2) )
    | ~ spl4_5 ),
    inference(superposition,[],[f31,f74])).

fof(f152,plain,
    ( spl4_15
    | ~ spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f144,f141,f150,f147])).

fof(f141,plain,
    ( spl4_14
  <=> ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f144,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f142,f54])).

fof(f142,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X1,sK2) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl4_7
    | spl4_14
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f77,f73,f141,f89])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | k1_xboole_0 = sK3
        | r1_tarski(X1,sK2) )
    | ~ spl4_5 ),
    inference(superposition,[],[f30,f74])).

fof(f128,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f126,f59])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f121,f63])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_8 ),
    inference(superposition,[],[f34,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f104,f89,f73,f92])).

fof(f104,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f102,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f74,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f98,plain,
    ( spl4_7
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f76,f73,f96,f89])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))
        | k1_xboole_0 = sK3
        | r1_tarski(sK2,X0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f30,f74])).

fof(f75,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f71,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f26,f69,f66])).

fof(f26,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (25602)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (25609)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (25619)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.51  % (25604)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.21/0.52  % (25605)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.52  % (25611)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.21/0.52  % (25613)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.53  % (25614)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.54  % (25603)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (25627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (25616)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (25620)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (25608)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (25607)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  % (25625)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.54  % (25618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.55  % (25628)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (25629)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.55  % (25623)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.55  % (25622)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.55  % (25615)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.55  % (25624)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.56  % (25606)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.56  % (25610)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.56  % (25612)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.56  % (25630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.57  % (25618)Refutation not found, incomplete strategy% (25618)------------------------------
% 1.34/0.57  % (25618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (25618)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.57  
% 1.34/0.57  % (25618)Memory used [KB]: 10618
% 1.34/0.57  % (25618)Time elapsed: 0.145 s
% 1.34/0.57  % (25618)------------------------------
% 1.34/0.57  % (25618)------------------------------
% 1.34/0.57  % (25626)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.57  % (25617)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.57  % (25621)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.58  % (25631)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.58  % (25631)Refutation not found, incomplete strategy% (25631)------------------------------
% 1.34/0.58  % (25631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (25631)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.58  
% 1.34/0.58  % (25631)Memory used [KB]: 1663
% 1.34/0.58  % (25631)Time elapsed: 0.156 s
% 1.34/0.58  % (25631)------------------------------
% 1.34/0.58  % (25631)------------------------------
% 2.52/0.70  % (25632)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.52/0.76  % (25633)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.32/0.83  % (25604)Time limit reached!
% 3.32/0.83  % (25604)------------------------------
% 3.32/0.83  % (25604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.84  % (25604)Termination reason: Time limit
% 3.55/0.84  
% 3.55/0.84  % (25604)Memory used [KB]: 7036
% 3.55/0.84  % (25604)Time elapsed: 0.418 s
% 3.55/0.84  % (25604)------------------------------
% 3.55/0.84  % (25604)------------------------------
% 3.55/0.84  % (25626)Time limit reached!
% 3.55/0.84  % (25626)------------------------------
% 3.55/0.84  % (25626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.84  % (25626)Termination reason: Time limit
% 3.55/0.84  % (25626)Termination phase: Saturation
% 3.55/0.84  
% 3.55/0.84  % (25626)Memory used [KB]: 12665
% 3.55/0.84  % (25626)Time elapsed: 0.400 s
% 3.55/0.84  % (25626)------------------------------
% 3.55/0.84  % (25626)------------------------------
% 4.25/0.93  % (25608)Time limit reached!
% 4.25/0.93  % (25608)------------------------------
% 4.25/0.93  % (25608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.93  % (25608)Termination reason: Time limit
% 4.25/0.93  
% 4.25/0.93  % (25608)Memory used [KB]: 14839
% 4.25/0.93  % (25608)Time elapsed: 0.518 s
% 4.25/0.93  % (25608)------------------------------
% 4.25/0.93  % (25608)------------------------------
% 4.25/0.95  % (25616)Time limit reached!
% 4.25/0.95  % (25616)------------------------------
% 4.25/0.95  % (25616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.96  % (25616)Termination reason: Time limit
% 4.25/0.96  % (25634)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.25/0.96  
% 4.25/0.96  % (25616)Memory used [KB]: 4349
% 4.25/0.96  % (25616)Time elapsed: 0.530 s
% 4.25/0.96  % (25616)------------------------------
% 4.25/0.96  % (25616)------------------------------
% 4.69/1.01  % (25635)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.69/1.02  % (25609)Time limit reached!
% 4.69/1.02  % (25609)------------------------------
% 4.69/1.02  % (25609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.69/1.02  % (25609)Termination reason: Time limit
% 4.69/1.02  % (25609)Termination phase: Saturation
% 4.69/1.02  
% 4.69/1.02  % (25609)Memory used [KB]: 5756
% 4.69/1.02  % (25609)Time elapsed: 0.600 s
% 4.69/1.02  % (25609)------------------------------
% 4.69/1.02  % (25609)------------------------------
% 5.64/1.09  % (25636)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.64/1.10  % (25637)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.10/1.19  % (25638)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.10/1.22  % (25603)Time limit reached!
% 6.10/1.22  % (25603)------------------------------
% 6.10/1.22  % (25603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.10/1.22  % (25603)Termination reason: Time limit
% 6.10/1.22  
% 6.10/1.22  % (25603)Memory used [KB]: 5117
% 6.10/1.22  % (25603)Time elapsed: 0.806 s
% 6.10/1.22  % (25603)------------------------------
% 6.10/1.22  % (25603)------------------------------
% 7.22/1.32  % (25639)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 7.79/1.36  % (25605)Time limit reached!
% 7.79/1.36  % (25605)------------------------------
% 7.79/1.36  % (25605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.79/1.36  % (25605)Termination reason: Time limit
% 7.79/1.36  
% 7.79/1.36  % (25605)Memory used [KB]: 7547
% 7.79/1.36  % (25605)Time elapsed: 0.927 s
% 7.79/1.36  % (25605)------------------------------
% 7.79/1.36  % (25605)------------------------------
% 8.24/1.42  % (25614)Time limit reached!
% 8.24/1.42  % (25614)------------------------------
% 8.24/1.42  % (25614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.24/1.42  % (25614)Termination reason: Time limit
% 8.24/1.42  
% 8.24/1.42  % (25614)Memory used [KB]: 14967
% 8.24/1.42  % (25614)Time elapsed: 1.008 s
% 8.24/1.42  % (25614)------------------------------
% 8.24/1.42  % (25614)------------------------------
% 8.24/1.43  % (25629)Time limit reached!
% 8.24/1.43  % (25629)------------------------------
% 8.24/1.43  % (25629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.46/1.44  % (25629)Termination reason: Time limit
% 8.46/1.44  % (25629)Termination phase: Saturation
% 8.46/1.44  
% 8.46/1.44  % (25629)Memory used [KB]: 14328
% 8.46/1.44  % (25629)Time elapsed: 1.0000 s
% 8.46/1.44  % (25629)------------------------------
% 8.46/1.44  % (25629)------------------------------
% 8.46/1.48  % (25640)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 9.44/1.60  % (25642)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.44/1.61  % (25641)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.44/1.62  % (25602)Time limit reached!
% 9.44/1.62  % (25602)------------------------------
% 9.44/1.62  % (25602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.44/1.63  % (25602)Termination reason: Time limit
% 9.44/1.63  
% 9.44/1.63  % (25602)Memory used [KB]: 9722
% 9.44/1.63  % (25602)Time elapsed: 1.204 s
% 9.44/1.63  % (25602)------------------------------
% 9.44/1.63  % (25602)------------------------------
% 9.44/1.65  % (25628)Refutation found. Thanks to Tanya!
% 9.44/1.65  % SZS status Theorem for theBenchmark
% 9.44/1.65  % SZS output start Proof for theBenchmark
% 9.44/1.65  fof(f16657,plain,(
% 9.44/1.65    $false),
% 9.44/1.65    inference(avatar_sat_refutation,[],[f60,f64,f71,f75,f98,f111,f128,f143,f152,f156,f171,f271,f290,f319,f781,f818,f889,f1160,f1327,f1713,f2227,f5332,f5427,f5831,f6160,f6183,f6491,f6683,f6821,f6850,f7680,f7832,f7899,f8899,f16298,f16462,f16567,f16643])).
% 9.44/1.65  fof(f16643,plain,(
% 9.44/1.65    spl4_2 | ~spl4_5 | ~spl4_26 | ~spl4_154 | ~spl4_166 | spl4_191 | ~spl4_221),
% 9.44/1.65    inference(avatar_contradiction_clause,[],[f16642])).
% 9.44/1.65  fof(f16642,plain,(
% 9.44/1.65    $false | (spl4_2 | ~spl4_5 | ~spl4_26 | ~spl4_154 | ~spl4_166 | spl4_191 | ~spl4_221)),
% 9.44/1.65    inference(subsumption_resolution,[],[f16641,f8898])).
% 9.44/1.65  fof(f8898,plain,(
% 9.44/1.65    ~r1_tarski(sK0,sK2) | spl4_191),
% 9.44/1.65    inference(avatar_component_clause,[],[f8897])).
% 9.44/1.65  fof(f8897,plain,(
% 9.44/1.65    spl4_191 <=> r1_tarski(sK0,sK2)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).
% 9.44/1.65  fof(f16641,plain,(
% 9.44/1.65    r1_tarski(sK0,sK2) | (spl4_2 | ~spl4_5 | ~spl4_26 | ~spl4_154 | ~spl4_166 | ~spl4_221)),
% 9.44/1.65    inference(forward_demodulation,[],[f16640,f7679])).
% 9.44/1.65  fof(f7679,plain,(
% 9.44/1.65    sK0 = k2_xboole_0(sK0,sK2) | ~spl4_166),
% 9.44/1.65    inference(avatar_component_clause,[],[f7678])).
% 9.44/1.65  fof(f7678,plain,(
% 9.44/1.65    spl4_166 <=> sK0 = k2_xboole_0(sK0,sK2)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).
% 9.44/1.65  fof(f16640,plain,(
% 9.44/1.65    r1_tarski(k2_xboole_0(sK0,sK2),sK2) | (spl4_2 | ~spl4_5 | ~spl4_26 | ~spl4_154 | ~spl4_221)),
% 9.44/1.65    inference(subsumption_resolution,[],[f16639,f56])).
% 9.44/1.65  fof(f56,plain,(
% 9.44/1.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 9.44/1.65    inference(equality_resolution,[],[f42])).
% 9.44/1.65  fof(f42,plain,(
% 9.44/1.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 9.44/1.65    inference(cnf_transformation,[],[f5])).
% 9.44/1.65  fof(f5,axiom,(
% 9.44/1.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 9.44/1.65  fof(f16639,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),sK2) | (spl4_2 | ~spl4_5 | ~spl4_26 | ~spl4_154 | ~spl4_221)),
% 9.44/1.65    inference(forward_demodulation,[],[f16638,f74])).
% 9.44/1.65  fof(f74,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) | ~spl4_5),
% 9.44/1.65    inference(avatar_component_clause,[],[f73])).
% 9.44/1.65  fof(f73,plain,(
% 9.44/1.65    spl4_5 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 9.44/1.65  fof(f16638,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),sK2) | (spl4_2 | ~spl4_26 | ~spl4_154 | ~spl4_221)),
% 9.44/1.65    inference(forward_demodulation,[],[f16539,f6849])).
% 9.44/1.65  fof(f6849,plain,(
% 9.44/1.65    sK3 = k2_xboole_0(sK1,sK3) | ~spl4_154),
% 9.44/1.65    inference(avatar_component_clause,[],[f6848])).
% 9.44/1.65  fof(f6848,plain,(
% 9.44/1.65    spl4_154 <=> sK3 = k2_xboole_0(sK1,sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).
% 9.44/1.65  fof(f16539,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),sK2) | (spl4_2 | ~spl4_26 | ~spl4_221)),
% 9.44/1.65    inference(superposition,[],[f491,f16461])).
% 9.44/1.65  fof(f16461,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | ~spl4_221),
% 9.44/1.65    inference(avatar_component_clause,[],[f16460])).
% 9.44/1.65  fof(f16460,plain,(
% 9.44/1.65    spl4_221 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_221])])).
% 9.44/1.65  fof(f491,plain,(
% 9.44/1.65    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X0)) ) | (spl4_2 | ~spl4_26)),
% 9.44/1.65    inference(subsumption_resolution,[],[f482,f63])).
% 9.44/1.65  fof(f63,plain,(
% 9.44/1.65    k1_xboole_0 != sK1 | spl4_2),
% 9.44/1.65    inference(avatar_component_clause,[],[f62])).
% 9.44/1.65  fof(f62,plain,(
% 9.44/1.65    spl4_2 <=> k1_xboole_0 = sK1),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 9.44/1.65  fof(f482,plain,(
% 9.44/1.65    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK1)) | k1_xboole_0 = sK1 | r1_tarski(k2_xboole_0(sK0,sK2),X0)) ) | ~spl4_26),
% 9.44/1.65    inference(superposition,[],[f30,f318])).
% 9.44/1.65  fof(f318,plain,(
% 9.44/1.65    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) | ~spl4_26),
% 9.44/1.65    inference(avatar_component_clause,[],[f317])).
% 9.44/1.65  fof(f317,plain,(
% 9.44/1.65    spl4_26 <=> k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 9.44/1.65  fof(f30,plain,(
% 9.44/1.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f24])).
% 9.44/1.65  fof(f24,plain,(
% 9.44/1.65    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 9.44/1.65    inference(ennf_transformation,[],[f17])).
% 9.44/1.65  fof(f17,axiom,(
% 9.44/1.65    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 9.44/1.65  fof(f16567,plain,(
% 9.44/1.65    ~spl4_17 | spl4_151 | ~spl4_221),
% 9.44/1.65    inference(avatar_contradiction_clause,[],[f16566])).
% 9.44/1.65  fof(f16566,plain,(
% 9.44/1.65    $false | (~spl4_17 | spl4_151 | ~spl4_221)),
% 9.44/1.65    inference(subsumption_resolution,[],[f16565,f6490])).
% 9.44/1.65  fof(f6490,plain,(
% 9.44/1.65    ~r1_tarski(sK3,sK1) | spl4_151),
% 9.44/1.65    inference(avatar_component_clause,[],[f6489])).
% 9.44/1.65  fof(f6489,plain,(
% 9.44/1.65    spl4_151 <=> r1_tarski(sK3,sK1)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).
% 9.44/1.65  fof(f16565,plain,(
% 9.44/1.65    r1_tarski(sK3,sK1) | (~spl4_17 | ~spl4_221)),
% 9.44/1.65    inference(subsumption_resolution,[],[f16497,f56])).
% 9.44/1.65  fof(f16497,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,sK1) | (~spl4_17 | ~spl4_221)),
% 9.44/1.65    inference(superposition,[],[f155,f16461])).
% 9.44/1.65  fof(f155,plain,(
% 9.44/1.65    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) | r1_tarski(sK3,X2)) ) | ~spl4_17),
% 9.44/1.65    inference(avatar_component_clause,[],[f154])).
% 9.44/1.65  fof(f154,plain,(
% 9.44/1.65    spl4_17 <=> ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) | r1_tarski(sK3,X2))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 9.44/1.65  fof(f16462,plain,(
% 9.44/1.65    spl4_221 | ~spl4_5 | ~spl4_154 | ~spl4_218),
% 9.44/1.65    inference(avatar_split_clause,[],[f16372,f16296,f6848,f73,f16460])).
% 9.44/1.65  fof(f16296,plain,(
% 9.44/1.65    spl4_218 <=> k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).
% 9.44/1.65  fof(f16372,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | (~spl4_5 | ~spl4_154 | ~spl4_218)),
% 9.44/1.65    inference(subsumption_resolution,[],[f7551,f16371])).
% 9.44/1.65  fof(f16371,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_154 | ~spl4_218)),
% 9.44/1.65    inference(forward_demodulation,[],[f16370,f74])).
% 9.44/1.65  fof(f16370,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_154 | ~spl4_218)),
% 9.44/1.65    inference(forward_demodulation,[],[f16369,f6849])).
% 9.44/1.65  fof(f16369,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_218)),
% 9.44/1.65    inference(trivial_inequality_removal,[],[f16361])).
% 9.44/1.65  fof(f16361,plain,(
% 9.44/1.65    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_218)),
% 9.44/1.65    inference(superposition,[],[f2983,f16297])).
% 9.44/1.65  fof(f16297,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl4_218),
% 9.44/1.65    inference(avatar_component_clause,[],[f16296])).
% 9.44/1.65  fof(f2983,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)),k2_zfmisc_1(sK2,X0))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f33,f581])).
% 9.44/1.65  fof(f581,plain,(
% 9.44/1.65    ( ! [X3] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X3)) = k4_xboole_0(k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)),k2_zfmisc_1(sK2,X3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f49,f246])).
% 9.44/1.65  fof(f246,plain,(
% 9.44/1.65    ( ! [X1] : (k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f84,f52])).
% 9.44/1.65  fof(f52,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f1])).
% 9.44/1.65  fof(f1,axiom,(
% 9.44/1.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 9.44/1.65  fof(f84,plain,(
% 9.44/1.65    ( ! [X7] : (k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f41,f74])).
% 9.44/1.65  fof(f41,plain,(
% 9.44/1.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 9.44/1.65    inference(cnf_transformation,[],[f18])).
% 9.44/1.65  fof(f18,axiom,(
% 9.44/1.65    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 9.44/1.65  fof(f49,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f12])).
% 9.44/1.65  fof(f12,axiom,(
% 9.44/1.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 9.44/1.65  fof(f33,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f6])).
% 9.44/1.65  fof(f6,axiom,(
% 9.44/1.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 9.44/1.65  fof(f7551,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_154)),
% 9.44/1.65    inference(forward_demodulation,[],[f7550,f74])).
% 9.44/1.65  fof(f7550,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK1) | (~spl4_5 | ~spl4_154)),
% 9.44/1.65    inference(forward_demodulation,[],[f7492,f74])).
% 9.44/1.65  fof(f7492,plain,(
% 9.44/1.65    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) | k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK2,sK1) | (~spl4_5 | ~spl4_154)),
% 9.44/1.65    inference(superposition,[],[f261,f6849])).
% 9.44/1.65  fof(f261,plain,(
% 9.44/1.65    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3)),k2_zfmisc_1(sK2,X2)) | k2_zfmisc_1(sK2,X2) = k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(resolution,[],[f253,f44])).
% 9.44/1.65  fof(f44,plain,(
% 9.44/1.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 9.44/1.65    inference(cnf_transformation,[],[f5])).
% 9.44/1.65  fof(f253,plain,(
% 9.44/1.65    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f47,f84])).
% 9.44/1.65  fof(f47,plain,(
% 9.44/1.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.44/1.65    inference(cnf_transformation,[],[f14])).
% 9.44/1.65  fof(f14,axiom,(
% 9.44/1.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 9.44/1.65  fof(f16298,plain,(
% 9.44/1.65    spl4_218 | ~spl4_5 | ~spl4_43 | ~spl4_55 | ~spl4_170 | ~spl4_174),
% 9.44/1.65    inference(avatar_split_clause,[],[f16253,f7897,f7830,f1158,f816,f73,f16296])).
% 9.44/1.65  fof(f816,plain,(
% 9.44/1.65    spl4_43 <=> sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 9.44/1.65  fof(f1158,plain,(
% 9.44/1.65    spl4_55 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 9.44/1.65  fof(f7830,plain,(
% 9.44/1.65    spl4_170 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).
% 9.44/1.65  fof(f7897,plain,(
% 9.44/1.65    spl4_174 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).
% 9.44/1.65  fof(f16253,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_43 | ~spl4_55 | ~spl4_170 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16252,f74])).
% 9.44/1.65  fof(f16252,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) | (~spl4_5 | ~spl4_43 | ~spl4_55 | ~spl4_170 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16251,f38])).
% 9.44/1.65  fof(f38,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f10])).
% 9.44/1.65  fof(f10,axiom,(
% 9.44/1.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 9.44/1.65  fof(f16251,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k1_xboole_0) | (~spl4_5 | ~spl4_43 | ~spl4_55 | ~spl4_170 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16250,f1159])).
% 9.44/1.65  fof(f1159,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | ~spl4_55),
% 9.44/1.65    inference(avatar_component_clause,[],[f1158])).
% 9.44/1.65  fof(f16250,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) | (~spl4_5 | ~spl4_43 | ~spl4_170 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16249,f54])).
% 9.44/1.65  fof(f54,plain,(
% 9.44/1.65    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 9.44/1.65    inference(equality_resolution,[],[f35])).
% 9.44/1.65  fof(f35,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f16])).
% 9.44/1.65  fof(f16,axiom,(
% 9.44/1.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 9.44/1.65  fof(f16249,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK1)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1))) | (~spl4_5 | ~spl4_43 | ~spl4_170 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16248,f7831])).
% 9.44/1.65  fof(f7831,plain,(
% 9.44/1.65    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_170),
% 9.44/1.65    inference(avatar_component_clause,[],[f7830])).
% 9.44/1.65  fof(f16248,plain,(
% 9.44/1.65    k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)) | (~spl4_5 | ~spl4_43 | ~spl4_174)),
% 9.44/1.65    inference(forward_demodulation,[],[f16234,f8257])).
% 9.44/1.65  fof(f8257,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),sK1) = k3_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | ~spl4_174),
% 9.44/1.65    inference(superposition,[],[f39,f7898])).
% 9.44/1.65  fof(f7898,plain,(
% 9.44/1.65    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_174),
% 9.44/1.65    inference(avatar_component_clause,[],[f7897])).
% 9.44/1.65  fof(f39,plain,(
% 9.44/1.65    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 9.44/1.65    inference(cnf_transformation,[],[f19])).
% 9.44/1.65  fof(f19,axiom,(
% 9.44/1.65    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 9.44/1.65  fof(f16234,plain,(
% 9.44/1.65    k3_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(k1_xboole_0,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) | (~spl4_5 | ~spl4_43)),
% 9.44/1.65    inference(superposition,[],[f4644,f817])).
% 9.44/1.65  fof(f817,plain,(
% 9.44/1.65    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl4_43),
% 9.44/1.65    inference(avatar_component_clause,[],[f816])).
% 9.44/1.65  fof(f4644,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f48,f636])).
% 9.44/1.65  fof(f636,plain,(
% 9.44/1.65    ( ! [X1] : (k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(forward_demodulation,[],[f633,f51])).
% 9.44/1.65  fof(f51,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f2])).
% 9.44/1.65  fof(f2,axiom,(
% 9.44/1.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.44/1.65  fof(f633,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3),k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f48,f205])).
% 9.44/1.65  fof(f205,plain,(
% 9.44/1.65    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X2,sK2),sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f49,f82])).
% 9.44/1.65  fof(f82,plain,(
% 9.44/1.65    ( ! [X5] : (k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f40,f74])).
% 9.44/1.65  fof(f40,plain,(
% 9.44/1.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 9.44/1.65    inference(cnf_transformation,[],[f18])).
% 9.44/1.65  fof(f48,plain,(
% 9.44/1.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.44/1.65    inference(cnf_transformation,[],[f13])).
% 9.44/1.65  fof(f13,axiom,(
% 9.44/1.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.44/1.65  fof(f8899,plain,(
% 9.44/1.65    spl4_4 | ~spl4_191 | ~spl4_149),
% 9.44/1.65    inference(avatar_split_clause,[],[f6262,f6158,f8897,f69])).
% 9.44/1.65  fof(f69,plain,(
% 9.44/1.65    spl4_4 <=> sK0 = sK2),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 9.44/1.65  fof(f6158,plain,(
% 9.44/1.65    spl4_149 <=> r1_tarski(sK2,sK0)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_149])])).
% 9.44/1.65  fof(f6262,plain,(
% 9.44/1.65    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_149),
% 9.44/1.65    inference(resolution,[],[f6159,f44])).
% 9.44/1.65  fof(f6159,plain,(
% 9.44/1.65    r1_tarski(sK2,sK0) | ~spl4_149),
% 9.44/1.65    inference(avatar_component_clause,[],[f6158])).
% 9.44/1.65  fof(f7899,plain,(
% 9.44/1.65    spl4_174 | ~spl4_83 | ~spl4_154),
% 9.44/1.65    inference(avatar_split_clause,[],[f7510,f6848,f1711,f7897])).
% 9.44/1.65  fof(f1711,plain,(
% 9.44/1.65    spl4_83 <=> ! [X0] : r1_tarski(X0,k2_xboole_0(sK3,X0))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 9.44/1.65  fof(f7510,plain,(
% 9.44/1.65    sK1 = k3_xboole_0(sK1,sK3) | (~spl4_83 | ~spl4_154)),
% 9.44/1.65    inference(superposition,[],[f1754,f6849])).
% 9.44/1.65  fof(f1754,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(X1,k2_xboole_0(X1,sK3)) = X1) ) | ~spl4_83),
% 9.44/1.65    inference(forward_demodulation,[],[f1752,f37])).
% 9.44/1.65  fof(f37,plain,(
% 9.44/1.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.44/1.65    inference(cnf_transformation,[],[f11])).
% 9.44/1.65  fof(f11,axiom,(
% 9.44/1.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 9.44/1.65  fof(f1752,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(X1,k2_xboole_0(X1,sK3)) = k4_xboole_0(X1,k1_xboole_0)) ) | ~spl4_83),
% 9.44/1.65    inference(superposition,[],[f48,f1731])).
% 9.44/1.65  fof(f1731,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,sK3))) ) | ~spl4_83),
% 9.44/1.65    inference(superposition,[],[f1721,f52])).
% 9.44/1.65  fof(f1721,plain,(
% 9.44/1.65    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK3,X2))) ) | ~spl4_83),
% 9.44/1.65    inference(resolution,[],[f1712,f32])).
% 9.44/1.65  fof(f32,plain,(
% 9.44/1.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 9.44/1.65    inference(cnf_transformation,[],[f6])).
% 9.44/1.65  fof(f1712,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK3,X0))) ) | ~spl4_83),
% 9.44/1.65    inference(avatar_component_clause,[],[f1711])).
% 9.44/1.65  fof(f7832,plain,(
% 9.44/1.65    spl4_170 | ~spl4_153),
% 9.44/1.65    inference(avatar_split_clause,[],[f7432,f6819,f7830])).
% 9.44/1.65  fof(f6819,plain,(
% 9.44/1.65    spl4_153 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).
% 9.44/1.65  fof(f7432,plain,(
% 9.44/1.65    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_153),
% 9.44/1.65    inference(forward_demodulation,[],[f7431,f37])).
% 9.44/1.65  fof(f7431,plain,(
% 9.44/1.65    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK0,sK2) | ~spl4_153),
% 9.44/1.65    inference(forward_demodulation,[],[f7429,f51])).
% 9.44/1.65  fof(f7429,plain,(
% 9.44/1.65    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,sK0) | ~spl4_153),
% 9.44/1.65    inference(superposition,[],[f48,f6820])).
% 9.44/1.65  fof(f6820,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl4_153),
% 9.44/1.65    inference(avatar_component_clause,[],[f6819])).
% 9.44/1.65  fof(f7680,plain,(
% 9.44/1.65    spl4_166 | ~spl4_152),
% 9.44/1.65    inference(avatar_split_clause,[],[f7322,f6681,f7678])).
% 9.44/1.65  fof(f6681,plain,(
% 9.44/1.65    spl4_152 <=> sK0 = k2_xboole_0(sK2,sK0)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).
% 9.44/1.65  fof(f7322,plain,(
% 9.44/1.65    sK0 = k2_xboole_0(sK0,sK2) | ~spl4_152),
% 9.44/1.65    inference(superposition,[],[f6682,f52])).
% 9.44/1.65  fof(f6682,plain,(
% 9.44/1.65    sK0 = k2_xboole_0(sK2,sK0) | ~spl4_152),
% 9.44/1.65    inference(avatar_component_clause,[],[f6681])).
% 9.44/1.65  fof(f6850,plain,(
% 9.44/1.65    spl4_154 | ~spl4_150),
% 9.44/1.65    inference(avatar_split_clause,[],[f6321,f6181,f6848])).
% 9.44/1.65  fof(f6181,plain,(
% 9.44/1.65    spl4_150 <=> r1_tarski(sK1,sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).
% 9.44/1.65  fof(f6321,plain,(
% 9.44/1.65    sK3 = k2_xboole_0(sK1,sK3) | ~spl4_150),
% 9.44/1.65    inference(resolution,[],[f6182,f45])).
% 9.44/1.65  fof(f45,plain,(
% 9.44/1.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 9.44/1.65    inference(cnf_transformation,[],[f25])).
% 9.44/1.65  fof(f25,plain,(
% 9.44/1.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 9.44/1.65    inference(ennf_transformation,[],[f7])).
% 9.44/1.65  fof(f7,axiom,(
% 9.44/1.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 9.44/1.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 9.44/1.65  fof(f6182,plain,(
% 9.44/1.65    r1_tarski(sK1,sK3) | ~spl4_150),
% 9.44/1.65    inference(avatar_component_clause,[],[f6181])).
% 9.44/1.65  fof(f6821,plain,(
% 9.44/1.65    spl4_153 | ~spl4_149),
% 9.44/1.65    inference(avatar_split_clause,[],[f6263,f6158,f6819])).
% 9.44/1.65  fof(f6263,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl4_149),
% 9.44/1.65    inference(resolution,[],[f6159,f32])).
% 9.44/1.65  fof(f6683,plain,(
% 9.44/1.65    spl4_152 | ~spl4_149),
% 9.44/1.65    inference(avatar_split_clause,[],[f6261,f6158,f6681])).
% 9.44/1.65  fof(f6261,plain,(
% 9.44/1.65    sK0 = k2_xboole_0(sK2,sK0) | ~spl4_149),
% 9.44/1.65    inference(resolution,[],[f6159,f45])).
% 9.44/1.65  fof(f6491,plain,(
% 9.44/1.65    ~spl4_151 | spl4_3 | ~spl4_150),
% 9.44/1.65    inference(avatar_split_clause,[],[f6324,f6181,f66,f6489])).
% 9.44/1.65  fof(f66,plain,(
% 9.44/1.65    spl4_3 <=> sK1 = sK3),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 9.44/1.65  fof(f6324,plain,(
% 9.44/1.65    ~r1_tarski(sK3,sK1) | (spl4_3 | ~spl4_150)),
% 9.44/1.65    inference(subsumption_resolution,[],[f6322,f67])).
% 9.44/1.65  fof(f67,plain,(
% 9.44/1.65    sK1 != sK3 | spl4_3),
% 9.44/1.65    inference(avatar_component_clause,[],[f66])).
% 9.44/1.65  fof(f6322,plain,(
% 9.44/1.65    ~r1_tarski(sK3,sK1) | sK1 = sK3 | ~spl4_150),
% 9.44/1.65    inference(resolution,[],[f6182,f44])).
% 9.44/1.65  fof(f6183,plain,(
% 9.44/1.65    spl4_150 | spl4_1 | ~spl4_148),
% 9.44/1.65    inference(avatar_split_clause,[],[f5981,f5829,f58,f6181])).
% 9.44/1.65  fof(f58,plain,(
% 9.44/1.65    spl4_1 <=> k1_xboole_0 = sK0),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 9.44/1.65  fof(f5829,plain,(
% 9.44/1.65    spl4_148 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).
% 9.44/1.65  fof(f5981,plain,(
% 9.44/1.65    r1_tarski(sK1,sK3) | (spl4_1 | ~spl4_148)),
% 9.44/1.65    inference(subsumption_resolution,[],[f5977,f59])).
% 9.44/1.65  fof(f59,plain,(
% 9.44/1.65    k1_xboole_0 != sK0 | spl4_1),
% 9.44/1.65    inference(avatar_component_clause,[],[f58])).
% 9.44/1.65  fof(f5977,plain,(
% 9.44/1.65    k1_xboole_0 = sK0 | r1_tarski(sK1,sK3) | ~spl4_148),
% 9.44/1.65    inference(resolution,[],[f5830,f31])).
% 9.44/1.65  fof(f31,plain,(
% 9.44/1.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 9.44/1.65    inference(cnf_transformation,[],[f24])).
% 9.44/1.65  fof(f5830,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl4_148),
% 9.44/1.65    inference(avatar_component_clause,[],[f5829])).
% 9.44/1.65  fof(f6160,plain,(
% 9.44/1.65    spl4_149 | ~spl4_9 | ~spl4_148),
% 9.44/1.65    inference(avatar_split_clause,[],[f5976,f5829,f96,f6158])).
% 9.44/1.65  fof(f96,plain,(
% 9.44/1.65    spl4_9 <=> ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 9.44/1.65  fof(f5976,plain,(
% 9.44/1.65    r1_tarski(sK2,sK0) | (~spl4_9 | ~spl4_148)),
% 9.44/1.65    inference(resolution,[],[f5830,f97])).
% 9.44/1.65  fof(f97,plain,(
% 9.44/1.65    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | r1_tarski(sK2,X0)) ) | ~spl4_9),
% 9.44/1.65    inference(avatar_component_clause,[],[f96])).
% 9.44/1.65  fof(f5831,plain,(
% 9.44/1.65    spl4_148 | ~spl4_94 | ~spl4_137),
% 9.44/1.65    inference(avatar_split_clause,[],[f5512,f5425,f2225,f5829])).
% 9.44/1.65  fof(f2225,plain,(
% 9.44/1.65    spl4_94 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 9.44/1.65  fof(f5425,plain,(
% 9.44/1.65    spl4_137 <=> k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 9.44/1.65  fof(f5512,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | (~spl4_94 | ~spl4_137)),
% 9.44/1.65    inference(superposition,[],[f2226,f5426])).
% 9.44/1.65  fof(f5426,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) | ~spl4_137),
% 9.44/1.65    inference(avatar_component_clause,[],[f5425])).
% 9.44/1.65  fof(f2226,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) | ~spl4_94),
% 9.44/1.65    inference(avatar_component_clause,[],[f2225])).
% 9.44/1.65  fof(f5427,plain,(
% 9.44/1.65    spl4_137 | ~spl4_131),
% 9.44/1.65    inference(avatar_split_clause,[],[f5378,f5330,f5425])).
% 9.44/1.65  fof(f5330,plain,(
% 9.44/1.65    spl4_131 <=> k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).
% 9.44/1.65  fof(f5378,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) | ~spl4_131),
% 9.44/1.65    inference(superposition,[],[f5331,f37])).
% 9.44/1.65  fof(f5331,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0) | ~spl4_131),
% 9.44/1.65    inference(avatar_component_clause,[],[f5330])).
% 9.44/1.65  fof(f5332,plain,(
% 9.44/1.65    spl4_131 | ~spl4_5 | ~spl4_9 | ~spl4_17 | ~spl4_22 | ~spl4_70 | ~spl4_94),
% 9.44/1.65    inference(avatar_split_clause,[],[f4591,f2225,f1325,f288,f154,f96,f73,f5330])).
% 9.44/1.65  fof(f288,plain,(
% 9.44/1.65    spl4_22 <=> k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 9.44/1.65  fof(f1325,plain,(
% 9.44/1.65    spl4_70 <=> ! [X0] : r1_tarski(X0,k2_xboole_0(sK2,X0))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 9.44/1.65  fof(f4591,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k1_xboole_0) | (~spl4_5 | ~spl4_9 | ~spl4_17 | ~spl4_22 | ~spl4_70 | ~spl4_94)),
% 9.44/1.65    inference(forward_demodulation,[],[f4590,f289])).
% 9.44/1.65  fof(f289,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3) | ~spl4_22),
% 9.44/1.65    inference(avatar_component_clause,[],[f288])).
% 9.44/1.65  fof(f4590,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k1_xboole_0) | (~spl4_5 | ~spl4_9 | ~spl4_17 | ~spl4_22 | ~spl4_70 | ~spl4_94)),
% 9.44/1.65    inference(forward_demodulation,[],[f4589,f2371])).
% 9.44/1.65  fof(f2371,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) | ~spl4_94),
% 9.44/1.65    inference(resolution,[],[f2226,f32])).
% 9.44/1.65  fof(f4589,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK3) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) | (~spl4_5 | ~spl4_9 | ~spl4_17 | ~spl4_22 | ~spl4_70)),
% 9.44/1.65    inference(forward_demodulation,[],[f4588,f760])).
% 9.44/1.65  fof(f760,plain,(
% 9.44/1.65    ( ! [X1] : (sK3 = k3_xboole_0(sK3,k2_xboole_0(X1,sK3))) ) | (~spl4_5 | ~spl4_17)),
% 9.44/1.65    inference(forward_demodulation,[],[f758,f37])).
% 9.44/1.65  fof(f758,plain,(
% 9.44/1.65    ( ! [X1] : (k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(X1,sK3))) ) | (~spl4_5 | ~spl4_17)),
% 9.44/1.65    inference(superposition,[],[f48,f732])).
% 9.44/1.65  fof(f732,plain,(
% 9.44/1.65    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X2,sK3))) ) | (~spl4_5 | ~spl4_17)),
% 9.44/1.65    inference(resolution,[],[f720,f32])).
% 9.44/1.65  fof(f720,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(sK3,k2_xboole_0(X0,sK3))) ) | (~spl4_5 | ~spl4_17)),
% 9.44/1.65    inference(resolution,[],[f239,f155])).
% 9.44/1.65  fof(f239,plain,(
% 9.44/1.65    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f226,f52])).
% 9.44/1.65  fof(f226,plain,(
% 9.44/1.65    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X3)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f47,f83])).
% 9.44/1.65  fof(f83,plain,(
% 9.44/1.65    ( ! [X6] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X6)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f41,f74])).
% 9.44/1.65  fof(f4588,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,k2_xboole_0(sK1,sK3))) | (~spl4_5 | ~spl4_9 | ~spl4_22 | ~spl4_70)),
% 9.44/1.65    inference(forward_demodulation,[],[f4587,f51])).
% 9.44/1.65  fof(f4587,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(sK0,k3_xboole_0(k2_xboole_0(sK1,sK3),sK3)) | (~spl4_5 | ~spl4_9 | ~spl4_22 | ~spl4_70)),
% 9.44/1.65    inference(forward_demodulation,[],[f4586,f1496])).
% 9.44/1.65  fof(f1496,plain,(
% 9.44/1.65    ( ! [X8,X7,X9] : (k2_zfmisc_1(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(k2_zfmisc_1(X7,X8),k2_zfmisc_1(k2_xboole_0(X7,sK2),X9))) ) | ~spl4_70),
% 9.44/1.65    inference(superposition,[],[f39,f1360])).
% 9.44/1.65  fof(f1360,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(X1,k2_xboole_0(X1,sK2)) = X1) ) | ~spl4_70),
% 9.44/1.65    inference(forward_demodulation,[],[f1358,f37])).
% 9.44/1.65  fof(f1358,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(X1,k2_xboole_0(X1,sK2)) = k4_xboole_0(X1,k1_xboole_0)) ) | ~spl4_70),
% 9.44/1.65    inference(superposition,[],[f48,f1340])).
% 9.44/1.65  fof(f1340,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,sK2))) ) | ~spl4_70),
% 9.44/1.65    inference(superposition,[],[f1330,f52])).
% 9.44/1.65  fof(f1330,plain,(
% 9.44/1.65    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(sK2,X2))) ) | ~spl4_70),
% 9.44/1.65    inference(resolution,[],[f1326,f32])).
% 9.44/1.65  fof(f1326,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK2,X0))) ) | ~spl4_70),
% 9.44/1.65    inference(avatar_component_clause,[],[f1325])).
% 9.44/1.65  fof(f4586,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)) | (~spl4_5 | ~spl4_9 | ~spl4_22)),
% 9.44/1.65    inference(forward_demodulation,[],[f4529,f282])).
% 9.44/1.65  fof(f282,plain,(
% 9.44/1.65    ( ! [X0] : (k2_xboole_0(X0,sK2) = k2_xboole_0(sK2,k2_xboole_0(X0,sK2))) ) | (~spl4_5 | ~spl4_9)),
% 9.44/1.65    inference(resolution,[],[f272,f45])).
% 9.44/1.65  fof(f272,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(X0,sK2))) ) | (~spl4_5 | ~spl4_9)),
% 9.44/1.65    inference(resolution,[],[f194,f97])).
% 9.44/1.65  fof(f194,plain,(
% 9.44/1.65    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f183,f52])).
% 9.44/1.65  fof(f183,plain,(
% 9.44/1.65    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f47,f81])).
% 9.44/1.65  fof(f81,plain,(
% 9.44/1.65    ( ! [X4] : (k2_zfmisc_1(k2_xboole_0(sK2,X4),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f40,f74])).
% 9.44/1.65  fof(f4529,plain,(
% 9.44/1.65    k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,k2_xboole_0(sK0,sK2)),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(k2_xboole_0(sK2,k2_xboole_0(sK0,sK2)),sK3)) | (~spl4_5 | ~spl4_22)),
% 9.44/1.65    inference(superposition,[],[f622,f289])).
% 9.44/1.65  fof(f622,plain,(
% 9.44/1.65    ( ! [X1] : (k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3))) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(forward_demodulation,[],[f608,f51])).
% 9.44/1.65  fof(f608,plain,(
% 9.44/1.65    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k2_zfmisc_1(X1,sK3)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X1,sK3)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f48,f182])).
% 9.44/1.65  fof(f182,plain,(
% 9.44/1.65    ( ! [X2] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X2,sK3)) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,X2),sK3),k2_zfmisc_1(X2,sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f49,f81])).
% 9.44/1.65  fof(f2227,plain,(
% 9.44/1.65    spl4_94 | ~spl4_5 | ~spl4_22),
% 9.44/1.65    inference(avatar_split_clause,[],[f386,f288,f73,f2225])).
% 9.44/1.65  fof(f386,plain,(
% 9.44/1.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) | (~spl4_5 | ~spl4_22)),
% 9.44/1.65    inference(superposition,[],[f194,f289])).
% 9.44/1.65  fof(f1713,plain,(
% 9.44/1.65    spl4_83 | spl4_6 | ~spl4_5),
% 9.44/1.65    inference(avatar_split_clause,[],[f736,f73,f86,f1711])).
% 9.44/1.65  fof(f86,plain,(
% 9.44/1.65    spl4_6 <=> k1_xboole_0 = sK2),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 9.44/1.65  fof(f736,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 = sK2 | r1_tarski(X0,k2_xboole_0(sK3,X0))) ) | ~spl4_5),
% 9.44/1.65    inference(resolution,[],[f265,f31])).
% 9.44/1.65  fof(f265,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f253,f52])).
% 9.44/1.65  fof(f1327,plain,(
% 9.44/1.65    spl4_70 | spl4_7 | ~spl4_5),
% 9.44/1.65    inference(avatar_split_clause,[],[f687,f73,f89,f1325])).
% 9.44/1.65  fof(f89,plain,(
% 9.44/1.65    spl4_7 <=> k1_xboole_0 = sK3),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 9.44/1.65  fof(f687,plain,(
% 9.44/1.65    ( ! [X0] : (k1_xboole_0 = sK3 | r1_tarski(X0,k2_xboole_0(sK2,X0))) ) | ~spl4_5),
% 9.44/1.65    inference(resolution,[],[f216,f30])).
% 9.44/1.65  fof(f216,plain,(
% 9.44/1.65    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f206,f52])).
% 9.44/1.65  fof(f206,plain,(
% 9.44/1.65    ( ! [X3] : (r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3))) ) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f47,f82])).
% 9.44/1.65  fof(f1160,plain,(
% 9.44/1.65    spl4_55 | ~spl4_5 | ~spl4_20 | ~spl4_38),
% 9.44/1.65    inference(avatar_split_clause,[],[f917,f779,f269,f73,f1158])).
% 9.44/1.65  fof(f269,plain,(
% 9.44/1.65    spl4_20 <=> k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3)),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 9.44/1.65  fof(f779,plain,(
% 9.44/1.65    spl4_38 <=> k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 9.44/1.65    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 9.44/1.65  fof(f917,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | (~spl4_5 | ~spl4_20 | ~spl4_38)),
% 9.44/1.65    inference(forward_demodulation,[],[f916,f780])).
% 9.44/1.65  fof(f780,plain,(
% 9.44/1.65    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | ~spl4_38),
% 9.44/1.65    inference(avatar_component_clause,[],[f779])).
% 9.44/1.65  fof(f916,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) | (~spl4_5 | ~spl4_20)),
% 9.44/1.65    inference(forward_demodulation,[],[f893,f270])).
% 9.44/1.65  fof(f270,plain,(
% 9.44/1.65    k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3) | ~spl4_20),
% 9.44/1.65    inference(avatar_component_clause,[],[f269])).
% 9.44/1.65  fof(f893,plain,(
% 9.44/1.65    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3)) | ~spl4_5),
% 9.44/1.65    inference(superposition,[],[f213,f54])).
% 9.44/1.65  fof(f213,plain,(
% 9.44/1.66    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3))) ) | ~spl4_5),
% 9.44/1.66    inference(resolution,[],[f206,f32])).
% 9.44/1.66  fof(f889,plain,(
% 9.44/1.66    spl4_16 | ~spl4_38),
% 9.44/1.66    inference(avatar_split_clause,[],[f801,f779,f150])).
% 9.44/1.66  fof(f150,plain,(
% 9.44/1.66    spl4_16 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 9.44/1.66    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 9.44/1.66  fof(f801,plain,(
% 9.44/1.66    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | ~spl4_38),
% 9.44/1.66    inference(superposition,[],[f47,f780])).
% 9.44/1.66  fof(f818,plain,(
% 9.44/1.66    spl4_43 | ~spl4_15),
% 9.44/1.66    inference(avatar_split_clause,[],[f805,f147,f816])).
% 9.44/1.66  fof(f147,plain,(
% 9.44/1.66    spl4_15 <=> r1_tarski(k1_xboole_0,sK2)),
% 9.44/1.66    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 9.44/1.66  fof(f805,plain,(
% 9.44/1.66    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl4_15),
% 9.44/1.66    inference(resolution,[],[f148,f45])).
% 9.44/1.66  fof(f148,plain,(
% 9.44/1.66    r1_tarski(k1_xboole_0,sK2) | ~spl4_15),
% 9.44/1.66    inference(avatar_component_clause,[],[f147])).
% 9.44/1.66  fof(f781,plain,(
% 9.44/1.66    spl4_38 | ~spl4_5 | ~spl4_20),
% 9.44/1.66    inference(avatar_split_clause,[],[f620,f269,f73,f779])).
% 9.44/1.66  fof(f620,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | (~spl4_5 | ~spl4_20)),
% 9.44/1.66    inference(forward_demodulation,[],[f619,f37])).
% 9.44/1.66  fof(f619,plain,(
% 9.44/1.66    k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | (~spl4_5 | ~spl4_20)),
% 9.44/1.66    inference(forward_demodulation,[],[f618,f37])).
% 9.44/1.66  fof(f618,plain,(
% 9.44/1.66    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k1_xboole_0) | (~spl4_5 | ~spl4_20)),
% 9.44/1.66    inference(forward_demodulation,[],[f617,f270])).
% 9.44/1.66  fof(f617,plain,(
% 9.44/1.66    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3),k1_xboole_0) | ~spl4_5),
% 9.44/1.66    inference(forward_demodulation,[],[f605,f502])).
% 9.44/1.66  fof(f502,plain,(
% 9.44/1.66    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3) = k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)) ) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f177,f82])).
% 9.44/1.66  fof(f177,plain,(
% 9.44/1.66    ( ! [X1] : (k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3)) ) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f81,f52])).
% 9.44/1.66  fof(f605,plain,(
% 9.44/1.66    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3),k1_xboole_0) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f182,f54])).
% 9.44/1.66  fof(f319,plain,(
% 9.44/1.66    spl4_26 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f231,f73,f317])).
% 9.44/1.66  fof(f231,plain,(
% 9.44/1.66    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) | ~spl4_5),
% 9.44/1.66    inference(forward_demodulation,[],[f222,f52])).
% 9.44/1.66  fof(f222,plain,(
% 9.44/1.66    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1)) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f83,f40])).
% 9.44/1.66  fof(f290,plain,(
% 9.44/1.66    spl4_22 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f187,f73,f288])).
% 9.44/1.66  fof(f187,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3) | ~spl4_5),
% 9.44/1.66    inference(forward_demodulation,[],[f176,f52])).
% 9.44/1.66  fof(f176,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f81,f41])).
% 9.44/1.66  fof(f271,plain,(
% 9.44/1.66    spl4_20 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f185,f73,f269])).
% 9.44/1.66  fof(f185,plain,(
% 9.44/1.66    k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3) | ~spl4_5),
% 9.44/1.66    inference(forward_demodulation,[],[f184,f52])).
% 9.44/1.66  fof(f184,plain,(
% 9.44/1.66    k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 9.44/1.66    inference(forward_demodulation,[],[f174,f52])).
% 9.44/1.66  fof(f174,plain,(
% 9.44/1.66    k2_zfmisc_1(k2_xboole_0(sK2,k1_xboole_0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f81,f54])).
% 9.44/1.66  fof(f171,plain,(
% 9.44/1.66    ~spl4_5 | ~spl4_6 | spl4_8),
% 9.44/1.66    inference(avatar_contradiction_clause,[],[f170])).
% 9.44/1.66  fof(f170,plain,(
% 9.44/1.66    $false | (~spl4_5 | ~spl4_6 | spl4_8)),
% 9.44/1.66    inference(subsumption_resolution,[],[f169,f93])).
% 9.44/1.66  fof(f93,plain,(
% 9.44/1.66    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl4_8),
% 9.44/1.66    inference(avatar_component_clause,[],[f92])).
% 9.44/1.66  fof(f92,plain,(
% 9.44/1.66    spl4_8 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 9.44/1.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 9.44/1.66  fof(f169,plain,(
% 9.44/1.66    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl4_5 | ~spl4_6)),
% 9.44/1.66    inference(forward_demodulation,[],[f167,f54])).
% 9.44/1.66  fof(f167,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK3) | (~spl4_5 | ~spl4_6)),
% 9.44/1.66    inference(superposition,[],[f74,f87])).
% 9.44/1.66  fof(f87,plain,(
% 9.44/1.66    k1_xboole_0 = sK2 | ~spl4_6),
% 9.44/1.66    inference(avatar_component_clause,[],[f86])).
% 9.44/1.66  fof(f156,plain,(
% 9.44/1.66    spl4_6 | spl4_17 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f78,f73,f154,f86])).
% 9.44/1.66  fof(f78,plain,(
% 9.44/1.66    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) | k1_xboole_0 = sK2 | r1_tarski(sK3,X2)) ) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f31,f74])).
% 9.44/1.66  fof(f152,plain,(
% 9.44/1.66    spl4_15 | ~spl4_16 | ~spl4_14),
% 9.44/1.66    inference(avatar_split_clause,[],[f144,f141,f150,f147])).
% 9.44/1.66  fof(f141,plain,(
% 9.44/1.66    spl4_14 <=> ! [X1] : (~r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X1,sK2))),
% 9.44/1.66    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 9.44/1.66  fof(f144,plain,(
% 9.44/1.66    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | r1_tarski(k1_xboole_0,sK2) | ~spl4_14),
% 9.44/1.66    inference(superposition,[],[f142,f54])).
% 9.44/1.66  fof(f142,plain,(
% 9.44/1.66    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X1,sK2)) ) | ~spl4_14),
% 9.44/1.66    inference(avatar_component_clause,[],[f141])).
% 9.44/1.66  fof(f143,plain,(
% 9.44/1.66    spl4_7 | spl4_14 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f77,f73,f141,f89])).
% 9.44/1.66  fof(f77,plain,(
% 9.44/1.66    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(X1,sK2)) ) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f30,f74])).
% 9.44/1.66  fof(f128,plain,(
% 9.44/1.66    spl4_1 | spl4_2 | ~spl4_8),
% 9.44/1.66    inference(avatar_contradiction_clause,[],[f127])).
% 9.44/1.66  fof(f127,plain,(
% 9.44/1.66    $false | (spl4_1 | spl4_2 | ~spl4_8)),
% 9.44/1.66    inference(subsumption_resolution,[],[f126,f59])).
% 9.44/1.66  fof(f126,plain,(
% 9.44/1.66    k1_xboole_0 = sK0 | (spl4_2 | ~spl4_8)),
% 9.44/1.66    inference(subsumption_resolution,[],[f121,f63])).
% 9.44/1.66  fof(f121,plain,(
% 9.44/1.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_8),
% 9.44/1.66    inference(trivial_inequality_removal,[],[f116])).
% 9.44/1.66  fof(f116,plain,(
% 9.44/1.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_8),
% 9.44/1.66    inference(superposition,[],[f34,f107])).
% 9.44/1.66  fof(f107,plain,(
% 9.44/1.66    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_8),
% 9.44/1.66    inference(avatar_component_clause,[],[f92])).
% 9.44/1.66  fof(f34,plain,(
% 9.44/1.66    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 9.44/1.66    inference(cnf_transformation,[],[f16])).
% 9.44/1.66  fof(f111,plain,(
% 9.44/1.66    spl4_8 | ~spl4_5 | ~spl4_7),
% 9.44/1.66    inference(avatar_split_clause,[],[f104,f89,f73,f92])).
% 9.44/1.66  fof(f104,plain,(
% 9.44/1.66    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl4_5 | ~spl4_7)),
% 9.44/1.66    inference(forward_demodulation,[],[f102,f53])).
% 9.44/1.66  fof(f53,plain,(
% 9.44/1.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 9.44/1.66    inference(equality_resolution,[],[f36])).
% 9.44/1.66  fof(f36,plain,(
% 9.44/1.66    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 9.44/1.66    inference(cnf_transformation,[],[f16])).
% 9.44/1.66  fof(f102,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 9.44/1.66    inference(superposition,[],[f74,f90])).
% 9.44/1.66  fof(f90,plain,(
% 9.44/1.66    k1_xboole_0 = sK3 | ~spl4_7),
% 9.44/1.66    inference(avatar_component_clause,[],[f89])).
% 9.44/1.66  fof(f98,plain,(
% 9.44/1.66    spl4_7 | spl4_9 | ~spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f76,f73,f96,f89])).
% 9.44/1.66  fof(f76,plain,(
% 9.44/1.66    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) | k1_xboole_0 = sK3 | r1_tarski(sK2,X0)) ) | ~spl4_5),
% 9.44/1.66    inference(superposition,[],[f30,f74])).
% 9.44/1.66  fof(f75,plain,(
% 9.44/1.66    spl4_5),
% 9.44/1.66    inference(avatar_split_clause,[],[f27,f73])).
% 9.44/1.66  fof(f27,plain,(
% 9.44/1.66    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 9.44/1.66    inference(cnf_transformation,[],[f23])).
% 9.44/1.66  fof(f23,plain,(
% 9.44/1.66    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 9.44/1.66    inference(flattening,[],[f22])).
% 9.44/1.66  fof(f22,plain,(
% 9.44/1.66    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 9.44/1.66    inference(ennf_transformation,[],[f21])).
% 9.44/1.66  fof(f21,negated_conjecture,(
% 9.44/1.66    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.44/1.66    inference(negated_conjecture,[],[f20])).
% 9.44/1.66  fof(f20,conjecture,(
% 9.44/1.66    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.44/1.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 9.44/1.66  fof(f71,plain,(
% 9.44/1.66    ~spl4_3 | ~spl4_4),
% 9.44/1.66    inference(avatar_split_clause,[],[f26,f69,f66])).
% 9.44/1.66  fof(f26,plain,(
% 9.44/1.66    sK0 != sK2 | sK1 != sK3),
% 9.44/1.66    inference(cnf_transformation,[],[f23])).
% 9.44/1.66  fof(f64,plain,(
% 9.44/1.66    ~spl4_2),
% 9.44/1.66    inference(avatar_split_clause,[],[f29,f62])).
% 9.44/1.66  fof(f29,plain,(
% 9.44/1.66    k1_xboole_0 != sK1),
% 9.44/1.66    inference(cnf_transformation,[],[f23])).
% 9.44/1.66  fof(f60,plain,(
% 9.44/1.66    ~spl4_1),
% 9.44/1.66    inference(avatar_split_clause,[],[f28,f58])).
% 9.44/1.66  fof(f28,plain,(
% 9.44/1.66    k1_xboole_0 != sK0),
% 9.44/1.66    inference(cnf_transformation,[],[f23])).
% 9.44/1.66  % SZS output end Proof for theBenchmark
% 9.44/1.66  % (25628)------------------------------
% 9.44/1.66  % (25628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.44/1.66  % (25628)Termination reason: Refutation
% 9.44/1.66  
% 9.44/1.66  % (25628)Memory used [KB]: 13944
% 9.44/1.66  % (25628)Time elapsed: 1.227 s
% 9.44/1.66  % (25628)------------------------------
% 9.44/1.66  % (25628)------------------------------
% 9.44/1.66  % (25601)Success in time 1.285 s
%------------------------------------------------------------------------------
