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
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 271 expanded)
%              Number of leaves         :   28 ( 122 expanded)
%              Depth                    :    8
%              Number of atoms          :  324 ( 739 expanded)
%              Number of equality atoms :  172 ( 513 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f59,f64,f95,f99,f107,f142,f175,f201,f215,f222,f234,f240,f293,f327,f330,f331,f408,f460,f467,f482])).

fof(f482,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f476,f75,f61,f83])).

fof(f83,plain,
    ( spl6_11
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f61,plain,
    ( spl6_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f75,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f476,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f475,f30])).

% (21313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f30,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f475,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f63,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f63,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f467,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f454,f79,f61,f83])).

fof(f79,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f454,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f453,f271])).

fof(f271,plain,(
    ! [X14] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X14) ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f453,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f452,f271])).

fof(f452,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f63,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f460,plain,
    ( spl6_1
    | spl6_2
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f35,f40,f308,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f308,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl6_25
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f408,plain,
    ( spl6_1
    | ~ spl6_15
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f400,f307,f139,f33])).

fof(f139,plain,
    ( spl6_15
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f400,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_15
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f395,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f395,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ spl6_15
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f309,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f309,plain,
    ( sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f307])).

fof(f331,plain,
    ( sK0 != sK3
    | k2_zfmisc_1(sK0,sK1) != k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k2_zfmisc_1(sK3,sK4) != k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f330,plain,
    ( spl6_1
    | spl6_2
    | spl6_5
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f328,f324,f52,f38,f33])).

fof(f52,plain,
    ( spl6_5
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f324,plain,
    ( spl6_27
  <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f328,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_27 ),
    inference(superposition,[],[f326,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f326,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f324])).

fof(f327,plain,
    ( spl6_1
    | spl6_9
    | spl6_27
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f320,f312,f324,f75,f33])).

fof(f312,plain,
    ( spl6_26
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f320,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK0
    | ~ spl6_26 ),
    inference(superposition,[],[f18,f314])).

fof(f314,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f312])).

fof(f293,plain,
    ( spl6_1
    | spl6_2
    | spl6_6
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f286,f237,f56,f38,f33])).

fof(f56,plain,
    ( spl6_6
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f237,plain,
    ( spl6_22
  <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f286,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_22 ),
    inference(superposition,[],[f239,f17])).

% (21304)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f239,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f237])).

fof(f240,plain,
    ( spl6_10
    | spl6_9
    | spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f227,f219,f237,f75,f79])).

fof(f219,plain,
    ( spl6_20
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f227,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_20 ),
    inference(superposition,[],[f17,f221])).

fof(f221,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f234,plain,
    ( spl6_21
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f223,f219,f212,f231])).

fof(f231,plain,
    ( spl6_21
  <=> k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f212,plain,
    ( spl6_19
  <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f223,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f214,f221])).

fof(f214,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f222,plain,
    ( spl6_15
    | spl6_3
    | spl6_20
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f216,f212,f219,f43,f139])).

fof(f43,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f216,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_19 ),
    inference(superposition,[],[f214,f17])).

fof(f215,plain,
    ( spl6_12
    | spl6_3
    | spl6_19
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f205,f198,f212,f43,f88])).

fof(f88,plain,
    ( spl6_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f198,plain,
    ( spl6_18
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f205,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_18 ),
    inference(superposition,[],[f17,f200])).

fof(f200,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f201,plain,
    ( spl6_18
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f143,f61,f48,f198])).

fof(f48,plain,
    ( spl6_4
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f143,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f63,f49])).

fof(f49,plain,
    ( sK2 = sK5
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f175,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f159,f88,f79,f75])).

fof(f159,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f156,f15])).

fof(f156,plain,
    ( k1_relat_1(k1_xboole_0) = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl6_12 ),
    inference(superposition,[],[f17,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f142,plain,
    ( spl6_15
    | spl6_3
    | spl6_4
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f131,f92,f48,f43,f139])).

fof(f92,plain,
    ( spl6_13
  <=> sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f131,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_13 ),
    inference(superposition,[],[f94,f18])).

fof(f94,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f107,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f45,f40,f35,f84,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f45,plain,
    ( k1_xboole_0 != sK2
    | spl6_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f99,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f98,f71,f61,f83])).

fof(f71,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f98,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f96,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f63,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f95,plain,
    ( spl6_12
    | spl6_8
    | spl6_13
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f69,f61,f92,f71,f88])).

fof(f69,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_7 ),
    inference(superposition,[],[f18,f63])).

fof(f64,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f11,f19,f19])).

fof(f11,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f59,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f10,f56,f52,f48])).

% (21303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f10,plain,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f14,f43])).

fof(f14,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f13,f38])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (21308)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (21300)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (21298)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (21315)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (21291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.52  % (21289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.52  % (21288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (21299)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.53  % (21307)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.53  % (21293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.53  % (21290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.53  % (21308)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f483,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f36,f41,f46,f59,f64,f95,f99,f107,f142,f175,f201,f215,f222,f234,f240,f293,f327,f330,f331,f408,f460,f467,f482])).
% 1.26/0.53  fof(f482,plain,(
% 1.26/0.53    spl6_11 | ~spl6_7 | ~spl6_9),
% 1.26/0.53    inference(avatar_split_clause,[],[f476,f75,f61,f83])).
% 1.26/0.53  fof(f83,plain,(
% 1.26/0.53    spl6_11 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.26/0.53  fof(f61,plain,(
% 1.26/0.53    spl6_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.26/0.53  fof(f75,plain,(
% 1.26/0.53    spl6_9 <=> k1_xboole_0 = sK4),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.26/0.53  fof(f476,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_7 | ~spl6_9)),
% 1.26/0.53    inference(forward_demodulation,[],[f475,f30])).
% 1.26/0.53  % (21313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2)) )),
% 1.26/0.53    inference(equality_resolution,[],[f26])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 != X1) )),
% 1.26/0.53    inference(definition_unfolding,[],[f22,f19])).
% 1.26/0.53  fof(f19,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 != X1) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.26/0.53  fof(f475,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0),sK5) | (~spl6_7 | ~spl6_9)),
% 1.26/0.53    inference(forward_demodulation,[],[f63,f77])).
% 1.26/0.53  fof(f77,plain,(
% 1.26/0.53    k1_xboole_0 = sK4 | ~spl6_9),
% 1.26/0.53    inference(avatar_component_clause,[],[f75])).
% 1.26/0.53  fof(f63,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) | ~spl6_7),
% 1.26/0.53    inference(avatar_component_clause,[],[f61])).
% 1.26/0.53  fof(f467,plain,(
% 1.26/0.53    spl6_11 | ~spl6_7 | ~spl6_10),
% 1.26/0.53    inference(avatar_split_clause,[],[f454,f79,f61,f83])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    spl6_10 <=> k1_xboole_0 = sK3),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.26/0.53  fof(f454,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_7 | ~spl6_10)),
% 1.26/0.53    inference(forward_demodulation,[],[f453,f271])).
% 1.26/0.53  fof(f271,plain,(
% 1.26/0.53    ( ! [X14] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X14)) )),
% 1.26/0.53    inference(superposition,[],[f30,f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    ( ! [X2,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 1.26/0.53    inference(equality_resolution,[],[f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 != X0) )),
% 1.26/0.53    inference(definition_unfolding,[],[f21,f19])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 != X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f453,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | (~spl6_7 | ~spl6_10)),
% 1.26/0.53    inference(forward_demodulation,[],[f452,f271])).
% 1.26/0.53  fof(f452,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4),sK5) | (~spl6_7 | ~spl6_10)),
% 1.26/0.53    inference(forward_demodulation,[],[f63,f81])).
% 1.26/0.53  fof(f81,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | ~spl6_10),
% 1.26/0.53    inference(avatar_component_clause,[],[f79])).
% 1.26/0.53  fof(f460,plain,(
% 1.26/0.53    spl6_1 | spl6_2 | spl6_25),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f457])).
% 1.26/0.53  fof(f457,plain,(
% 1.26/0.53    $false | (spl6_1 | spl6_2 | spl6_25)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f35,f40,f308,f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,plain,(
% 1.26/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.26/0.53    inference(ennf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.26/0.53  fof(f308,plain,(
% 1.26/0.53    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_25),
% 1.26/0.53    inference(avatar_component_clause,[],[f307])).
% 1.26/0.53  fof(f307,plain,(
% 1.26/0.53    spl6_25 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    k1_xboole_0 != sK1 | spl6_2),
% 1.26/0.53    inference(avatar_component_clause,[],[f38])).
% 1.26/0.53  fof(f38,plain,(
% 1.26/0.53    spl6_2 <=> k1_xboole_0 = sK1),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.26/0.53  fof(f35,plain,(
% 1.26/0.53    k1_xboole_0 != sK0 | spl6_1),
% 1.26/0.53    inference(avatar_component_clause,[],[f33])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    spl6_1 <=> k1_xboole_0 = sK0),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.26/0.53  fof(f408,plain,(
% 1.26/0.53    spl6_1 | ~spl6_15 | ~spl6_25),
% 1.26/0.53    inference(avatar_split_clause,[],[f400,f307,f139,f33])).
% 1.26/0.53  fof(f139,plain,(
% 1.26/0.53    spl6_15 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.26/0.53  fof(f400,plain,(
% 1.26/0.53    k1_xboole_0 = sK0 | (~spl6_15 | ~spl6_25)),
% 1.26/0.53    inference(forward_demodulation,[],[f395,f15])).
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.53    inference(cnf_transformation,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.26/0.53  fof(f395,plain,(
% 1.26/0.53    k1_relat_1(k1_xboole_0) = sK0 | (~spl6_15 | ~spl6_25)),
% 1.26/0.53    inference(backward_demodulation,[],[f309,f141])).
% 1.26/0.53  fof(f141,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_15),
% 1.26/0.53    inference(avatar_component_clause,[],[f139])).
% 1.26/0.53  fof(f309,plain,(
% 1.26/0.53    sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl6_25),
% 1.26/0.53    inference(avatar_component_clause,[],[f307])).
% 1.26/0.53  fof(f331,plain,(
% 1.26/0.53    sK0 != sK3 | k2_zfmisc_1(sK0,sK1) != k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k2_zfmisc_1(sK3,sK4) != k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4)),
% 1.26/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.26/0.53  fof(f330,plain,(
% 1.26/0.53    spl6_1 | spl6_2 | spl6_5 | ~spl6_27),
% 1.26/0.53    inference(avatar_split_clause,[],[f328,f324,f52,f38,f33])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    spl6_5 <=> sK1 = sK4),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.26/0.53  fof(f324,plain,(
% 1.26/0.53    spl6_27 <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.26/0.53  fof(f328,plain,(
% 1.26/0.53    sK1 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_27),
% 1.26/0.53    inference(superposition,[],[f326,f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f326,plain,(
% 1.26/0.53    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl6_27),
% 1.26/0.53    inference(avatar_component_clause,[],[f324])).
% 1.26/0.53  fof(f327,plain,(
% 1.26/0.53    spl6_1 | spl6_9 | spl6_27 | ~spl6_26),
% 1.26/0.53    inference(avatar_split_clause,[],[f320,f312,f324,f75,f33])).
% 1.26/0.53  fof(f312,plain,(
% 1.26/0.53    spl6_26 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.26/0.53  fof(f320,plain,(
% 1.26/0.53    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK0 | ~spl6_26),
% 1.26/0.53    inference(superposition,[],[f18,f314])).
% 1.26/0.53  fof(f314,plain,(
% 1.26/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK4) | ~spl6_26),
% 1.26/0.53    inference(avatar_component_clause,[],[f312])).
% 1.26/0.53  fof(f293,plain,(
% 1.26/0.53    spl6_1 | spl6_2 | spl6_6 | ~spl6_22),
% 1.26/0.53    inference(avatar_split_clause,[],[f286,f237,f56,f38,f33])).
% 1.26/0.53  fof(f56,plain,(
% 1.26/0.53    spl6_6 <=> sK0 = sK3),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.26/0.53  fof(f237,plain,(
% 1.26/0.53    spl6_22 <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.26/0.53  fof(f286,plain,(
% 1.26/0.53    sK0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_22),
% 1.26/0.53    inference(superposition,[],[f239,f17])).
% 1.26/0.53  % (21304)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.26/0.53  fof(f239,plain,(
% 1.26/0.53    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl6_22),
% 1.26/0.53    inference(avatar_component_clause,[],[f237])).
% 1.26/0.53  fof(f240,plain,(
% 1.26/0.53    spl6_10 | spl6_9 | spl6_22 | ~spl6_20),
% 1.26/0.53    inference(avatar_split_clause,[],[f227,f219,f237,f75,f79])).
% 1.26/0.53  fof(f219,plain,(
% 1.26/0.53    spl6_20 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.26/0.53  fof(f227,plain,(
% 1.26/0.53    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl6_20),
% 1.26/0.53    inference(superposition,[],[f17,f221])).
% 1.26/0.53  fof(f221,plain,(
% 1.26/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~spl6_20),
% 1.26/0.53    inference(avatar_component_clause,[],[f219])).
% 1.26/0.53  fof(f234,plain,(
% 1.26/0.53    spl6_21 | ~spl6_19 | ~spl6_20),
% 1.26/0.53    inference(avatar_split_clause,[],[f223,f219,f212,f231])).
% 1.26/0.53  fof(f231,plain,(
% 1.26/0.53    spl6_21 <=> k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.26/0.53  fof(f212,plain,(
% 1.26/0.53    spl6_19 <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.26/0.53  fof(f223,plain,(
% 1.26/0.53    k2_zfmisc_1(sK0,sK1) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl6_19 | ~spl6_20)),
% 1.26/0.53    inference(backward_demodulation,[],[f214,f221])).
% 1.26/0.53  fof(f214,plain,(
% 1.26/0.53    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_19),
% 1.26/0.53    inference(avatar_component_clause,[],[f212])).
% 1.26/0.53  fof(f222,plain,(
% 1.26/0.53    spl6_15 | spl6_3 | spl6_20 | ~spl6_19),
% 1.26/0.53    inference(avatar_split_clause,[],[f216,f212,f219,f43,f139])).
% 1.26/0.53  fof(f43,plain,(
% 1.26/0.53    spl6_3 <=> k1_xboole_0 = sK2),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.26/0.53  fof(f216,plain,(
% 1.26/0.53    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_19),
% 1.26/0.53    inference(superposition,[],[f214,f17])).
% 1.26/0.53  fof(f215,plain,(
% 1.26/0.53    spl6_12 | spl6_3 | spl6_19 | ~spl6_18),
% 1.26/0.53    inference(avatar_split_clause,[],[f205,f198,f212,f43,f88])).
% 1.26/0.53  fof(f88,plain,(
% 1.26/0.53    spl6_12 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.26/0.53  fof(f198,plain,(
% 1.26/0.53    spl6_18 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.26/0.53  fof(f205,plain,(
% 1.26/0.53    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl6_18),
% 1.26/0.53    inference(superposition,[],[f17,f200])).
% 1.26/0.53  fof(f200,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2) | ~spl6_18),
% 1.26/0.53    inference(avatar_component_clause,[],[f198])).
% 1.26/0.53  fof(f201,plain,(
% 1.26/0.53    spl6_18 | ~spl6_4 | ~spl6_7),
% 1.26/0.53    inference(avatar_split_clause,[],[f143,f61,f48,f198])).
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    spl6_4 <=> sK2 = sK5),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.26/0.53  fof(f143,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2) | (~spl6_4 | ~spl6_7)),
% 1.26/0.53    inference(backward_demodulation,[],[f63,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    sK2 = sK5 | ~spl6_4),
% 1.26/0.53    inference(avatar_component_clause,[],[f48])).
% 1.26/0.53  fof(f175,plain,(
% 1.26/0.53    spl6_9 | spl6_10 | ~spl6_12),
% 1.26/0.53    inference(avatar_split_clause,[],[f159,f88,f79,f75])).
% 1.26/0.53  fof(f159,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl6_12),
% 1.26/0.53    inference(duplicate_literal_removal,[],[f158])).
% 1.26/0.53  fof(f158,plain,(
% 1.26/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl6_12),
% 1.26/0.53    inference(forward_demodulation,[],[f156,f15])).
% 1.26/0.53  fof(f156,plain,(
% 1.26/0.53    k1_relat_1(k1_xboole_0) = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | ~spl6_12),
% 1.26/0.53    inference(superposition,[],[f17,f90])).
% 1.26/0.53  fof(f90,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl6_12),
% 1.26/0.53    inference(avatar_component_clause,[],[f88])).
% 1.26/0.53  fof(f142,plain,(
% 1.26/0.53    spl6_15 | spl6_3 | spl6_4 | ~spl6_13),
% 1.26/0.53    inference(avatar_split_clause,[],[f131,f92,f48,f43,f139])).
% 1.26/0.53  fof(f92,plain,(
% 1.26/0.53    spl6_13 <=> sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.26/0.53  fof(f131,plain,(
% 1.26/0.53    sK2 = sK5 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_13),
% 1.26/0.53    inference(superposition,[],[f94,f18])).
% 1.26/0.53  fof(f94,plain,(
% 1.26/0.53    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl6_13),
% 1.26/0.53    inference(avatar_component_clause,[],[f92])).
% 1.26/0.53  fof(f107,plain,(
% 1.26/0.53    spl6_1 | spl6_2 | spl6_3 | ~spl6_11),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f100])).
% 1.26/0.53  fof(f100,plain,(
% 1.26/0.53    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_11)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f45,f40,f35,f84,f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.26/0.53    inference(definition_unfolding,[],[f20,f19])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f84,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_11),
% 1.26/0.53    inference(avatar_component_clause,[],[f83])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    k1_xboole_0 != sK2 | spl6_3),
% 1.26/0.53    inference(avatar_component_clause,[],[f43])).
% 1.26/0.53  fof(f99,plain,(
% 1.26/0.53    spl6_11 | ~spl6_7 | ~spl6_8),
% 1.26/0.53    inference(avatar_split_clause,[],[f98,f71,f61,f83])).
% 1.26/0.53  fof(f71,plain,(
% 1.26/0.53    spl6_8 <=> k1_xboole_0 = sK5),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.26/0.53  fof(f98,plain,(
% 1.26/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl6_7 | ~spl6_8)),
% 1.26/0.53    inference(forward_demodulation,[],[f96,f29])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f25])).
% 1.26/0.53  fof(f25,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 != X2) )),
% 1.26/0.53    inference(definition_unfolding,[],[f23,f19])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 != X2) )),
% 1.26/0.53    inference(cnf_transformation,[],[f4])).
% 1.26/0.53  fof(f96,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0) | (~spl6_7 | ~spl6_8)),
% 1.26/0.53    inference(backward_demodulation,[],[f63,f73])).
% 1.26/0.53  fof(f73,plain,(
% 1.26/0.53    k1_xboole_0 = sK5 | ~spl6_8),
% 1.26/0.53    inference(avatar_component_clause,[],[f71])).
% 1.26/0.53  fof(f95,plain,(
% 1.26/0.53    spl6_12 | spl6_8 | spl6_13 | ~spl6_7),
% 1.26/0.53    inference(avatar_split_clause,[],[f69,f61,f92,f71,f88])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl6_7),
% 1.26/0.53    inference(superposition,[],[f18,f63])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    spl6_7),
% 1.26/0.53    inference(avatar_split_clause,[],[f24,f61])).
% 1.26/0.53  fof(f24,plain,(
% 1.26/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 1.26/0.53    inference(definition_unfolding,[],[f11,f19,f19])).
% 1.26/0.53  fof(f11,plain,(
% 1.26/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.26/0.53    inference(flattening,[],[f7])).
% 1.26/0.53  fof(f7,plain,(
% 1.26/0.53    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.26/0.53    inference(ennf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,negated_conjecture,(
% 1.26/0.53    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.26/0.53    inference(negated_conjecture,[],[f5])).
% 1.26/0.53  fof(f5,conjecture,(
% 1.26/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.26/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).
% 1.26/0.53  fof(f59,plain,(
% 1.26/0.53    ~spl6_4 | ~spl6_5 | ~spl6_6),
% 1.26/0.53    inference(avatar_split_clause,[],[f10,f56,f52,f48])).
% 1.26/0.53  % (21303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.26/0.53  fof(f10,plain,(
% 1.26/0.53    sK0 != sK3 | sK1 != sK4 | sK2 != sK5),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f46,plain,(
% 1.26/0.53    ~spl6_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f14,f43])).
% 1.26/0.53  fof(f14,plain,(
% 1.26/0.53    k1_xboole_0 != sK2),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f41,plain,(
% 1.26/0.53    ~spl6_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f13,f38])).
% 1.26/0.53  fof(f13,plain,(
% 1.26/0.53    k1_xboole_0 != sK1),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f36,plain,(
% 1.26/0.53    ~spl6_1),
% 1.26/0.53    inference(avatar_split_clause,[],[f12,f33])).
% 1.26/0.53  fof(f12,plain,(
% 1.26/0.53    k1_xboole_0 != sK0),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (21308)------------------------------
% 1.26/0.53  % (21308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (21308)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (21308)Memory used [KB]: 11001
% 1.26/0.53  % (21308)Time elapsed: 0.076 s
% 1.26/0.53  % (21308)------------------------------
% 1.26/0.53  % (21308)------------------------------
% 1.26/0.54  % (21294)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (21285)Success in time 0.177 s
%------------------------------------------------------------------------------
