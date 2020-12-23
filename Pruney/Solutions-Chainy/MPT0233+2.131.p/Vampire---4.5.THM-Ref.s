%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 181 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  272 ( 468 expanded)
%              Number of equality atoms :  120 ( 233 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f165,f204,f241,f252,f322,f323,f336,f361,f394,f438,f483,f495,f496,f550])).

fof(f550,plain,
    ( spl4_2
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | spl4_2
    | ~ spl4_17 ),
    inference(trivial_inequality_removal,[],[f545])).

fof(f545,plain,
    ( sK0 != sK0
    | spl4_2
    | ~ spl4_17 ),
    inference(superposition,[],[f62,f251])).

fof(f251,plain,
    ( ! [X1] : sK0 = X1
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl4_17
  <=> ! [X1] : sK0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f62,plain,
    ( sK0 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f496,plain,
    ( spl4_10
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f477,f397,f124])).

fof(f124,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f397,plain,
    ( spl4_33
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f477,plain,
    ( sK0 = sK1
    | ~ spl4_33 ),
    inference(resolution,[],[f452,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f452,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(X0),k2_tarski(sK0,sK1))
        | sK1 = X0 )
    | ~ spl4_33 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(X0),k2_tarski(sK0,sK1))
        | sK1 = X0
        | sK1 = X0 )
    | ~ spl4_33 ),
    inference(superposition,[],[f30,f399])).

fof(f399,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f397])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f495,plain,
    ( spl4_5
    | spl4_6
    | spl4_7
    | spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f222,f65,f104,f100,f96,f82])).

fof(f82,plain,
    ( spl4_5
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f96,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( spl4_7
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f104,plain,
    ( spl4_8
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f65,plain,
    ( spl4_3
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f222,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f67,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f67,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f483,plain,
    ( sK0 != sK1
    | sK1 != sK2
    | sK0 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f438,plain,
    ( spl4_33
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f436,f363,f358,f397])).

fof(f358,plain,
    ( spl4_30
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f363,plain,
    ( spl4_31
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f436,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f360,f364])).

fof(f364,plain,
    ( sK1 = sK3
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f363])).

fof(f360,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f358])).

fof(f394,plain,
    ( spl4_31
    | spl4_1
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f389,f288,f55,f363])).

fof(f55,plain,
    ( spl4_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f288,plain,
    ( spl4_22
  <=> r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f389,plain,
    ( sK1 = sK3
    | spl4_1
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f385,f57])).

fof(f57,plain,
    ( sK0 != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f385,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl4_22 ),
    inference(resolution,[],[f290,f30])).

fof(f290,plain,
    ( r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f288])).

fof(f361,plain,
    ( spl4_30
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f354,f333,f82,f358])).

fof(f333,plain,
    ( spl4_26
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f354,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3)
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f84,f335])).

fof(f335,plain,
    ( sK1 = sK2
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f333])).

fof(f84,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f336,plain,
    ( spl4_26
    | spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f331,f283,f60,f333])).

fof(f283,plain,
    ( spl4_21
  <=> r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f331,plain,
    ( sK1 = sK2
    | spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f328,f62])).

fof(f328,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl4_21 ),
    inference(resolution,[],[f285,f30])).

fof(f285,plain,
    ( r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f283])).

fof(f323,plain,
    ( spl4_22
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f317,f82,f288])).

fof(f317,plain,
    ( r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f84])).

fof(f49,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

% (3895)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f322,plain,
    ( spl4_21
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f316,f82,f283])).

fof(f316,plain,
    ( r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f44,f84])).

fof(f252,plain,
    ( spl4_17
    | spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f248,f143,f250,f250])).

fof(f143,plain,
    ( spl4_14
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( sK0 = X0
        | sK0 = X1 )
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f243,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
        | sK0 = X0
        | sK0 = X1 )
    | ~ spl4_14 ),
    inference(superposition,[],[f30,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f241,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f57,f106,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f106,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f204,plain,
    ( spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_2
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f62,f102,f36])).

fof(f102,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f165,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f164,f96,f143])).

fof(f164,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f159,f70])).

fof(f159,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(superposition,[],[f75,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f75,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_tarski(X2,X3),k1_tarski(X2))
      | k1_tarski(X2) = k2_tarski(X2,X3) ) ),
    inference(resolution,[],[f42,f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f20])).

% (3908)Refutation not found, incomplete strategy% (3908)------------------------------
% (3908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3895)Refutation not found, incomplete strategy% (3895)------------------------------
% (3895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3895)Termination reason: Refutation not found, incomplete strategy

% (3895)Memory used [KB]: 1663
% (3895)Time elapsed: 0.131 s
% (3895)------------------------------
% (3895)------------------------------
% (3923)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (3910)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (3906)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (3919)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (3908)Termination reason: Refutation not found, incomplete strategy

% (3910)Refutation not found, incomplete strategy% (3910)------------------------------
% (3910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3910)Termination reason: Refutation not found, incomplete strategy

% (3910)Memory used [KB]: 10618
% (3910)Time elapsed: 0.182 s
% (3910)------------------------------
% (3910)------------------------------
% (3908)Memory used [KB]: 1918
% (3908)Time elapsed: 0.165 s
% (3908)------------------------------
% (3908)------------------------------
% (3921)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (3906)Refutation not found, incomplete strategy% (3906)------------------------------
% (3906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3906)Termination reason: Refutation not found, incomplete strategy

% (3906)Memory used [KB]: 10618
% (3906)Time elapsed: 0.181 s
% (3906)------------------------------
% (3906)------------------------------
fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f63,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:04:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (3899)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (3915)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (3897)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (3907)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (3894)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (3916)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (3905)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.58  % (3908)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.59  % (3898)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.59  % (3915)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.60  % (3900)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (3896)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.60  % (3920)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f560,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(avatar_sat_refutation,[],[f58,f63,f68,f165,f204,f241,f252,f322,f323,f336,f361,f394,f438,f483,f495,f496,f550])).
% 0.22/0.60  fof(f550,plain,(
% 0.22/0.60    spl4_2 | ~spl4_17),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f549])).
% 0.22/0.60  fof(f549,plain,(
% 0.22/0.60    $false | (spl4_2 | ~spl4_17)),
% 0.22/0.60    inference(trivial_inequality_removal,[],[f545])).
% 0.22/0.60  fof(f545,plain,(
% 0.22/0.60    sK0 != sK0 | (spl4_2 | ~spl4_17)),
% 0.22/0.60    inference(superposition,[],[f62,f251])).
% 0.22/0.60  fof(f251,plain,(
% 0.22/0.60    ( ! [X1] : (sK0 = X1) ) | ~spl4_17),
% 0.22/0.60    inference(avatar_component_clause,[],[f250])).
% 0.22/0.60  fof(f250,plain,(
% 0.22/0.60    spl4_17 <=> ! [X1] : sK0 = X1),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    sK0 != sK2 | spl4_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f60])).
% 0.22/0.60  fof(f60,plain,(
% 0.22/0.60    spl4_2 <=> sK0 = sK2),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.60  fof(f496,plain,(
% 0.22/0.60    spl4_10 | ~spl4_33),
% 0.22/0.60    inference(avatar_split_clause,[],[f477,f397,f124])).
% 0.22/0.60  fof(f124,plain,(
% 0.22/0.60    spl4_10 <=> sK0 = sK1),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.60  fof(f397,plain,(
% 0.22/0.60    spl4_33 <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.60  fof(f477,plain,(
% 0.22/0.60    sK0 = sK1 | ~spl4_33),
% 0.22/0.60    inference(resolution,[],[f452,f44])).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,axiom,(
% 0.22/0.60    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.60  fof(f452,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k2_tarski(sK0,sK1)) | sK1 = X0) ) | ~spl4_33),
% 0.22/0.60    inference(duplicate_literal_removal,[],[f443])).
% 0.22/0.60  fof(f443,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k2_tarski(sK0,sK1)) | sK1 = X0 | sK1 = X0) ) | ~spl4_33),
% 0.22/0.60    inference(superposition,[],[f30,f399])).
% 0.22/0.60  fof(f399,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl4_33),
% 0.22/0.60    inference(avatar_component_clause,[],[f397])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.22/0.60  fof(f495,plain,(
% 0.22/0.60    spl4_5 | spl4_6 | spl4_7 | spl4_8 | ~spl4_3),
% 0.22/0.60    inference(avatar_split_clause,[],[f222,f65,f104,f100,f96,f82])).
% 0.22/0.60  fof(f82,plain,(
% 0.22/0.60    spl4_5 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.60  fof(f96,plain,(
% 0.22/0.60    spl4_6 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.60  fof(f100,plain,(
% 0.22/0.60    spl4_7 <=> k2_tarski(sK0,sK1) = k1_tarski(sK2)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.60  fof(f104,plain,(
% 0.22/0.60    spl4_8 <=> k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    spl4_3 <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.60  fof(f222,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl4_3),
% 0.22/0.60    inference(resolution,[],[f67,f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.60    inference(flattening,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.60    inference(nnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.60  fof(f67,plain,(
% 0.22/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) | ~spl4_3),
% 0.22/0.60    inference(avatar_component_clause,[],[f65])).
% 0.22/0.60  fof(f483,plain,(
% 0.22/0.60    sK0 != sK1 | sK1 != sK2 | sK0 = sK2),
% 0.22/0.60    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.60  fof(f438,plain,(
% 0.22/0.60    spl4_33 | ~spl4_30 | ~spl4_31),
% 0.22/0.60    inference(avatar_split_clause,[],[f436,f363,f358,f397])).
% 0.22/0.60  fof(f358,plain,(
% 0.22/0.60    spl4_30 <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.60  fof(f363,plain,(
% 0.22/0.60    spl4_31 <=> sK1 = sK3),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.60  fof(f436,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) | (~spl4_30 | ~spl4_31)),
% 0.22/0.60    inference(backward_demodulation,[],[f360,f364])).
% 0.22/0.60  fof(f364,plain,(
% 0.22/0.60    sK1 = sK3 | ~spl4_31),
% 0.22/0.60    inference(avatar_component_clause,[],[f363])).
% 0.22/0.60  fof(f360,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3) | ~spl4_30),
% 0.22/0.60    inference(avatar_component_clause,[],[f358])).
% 0.22/0.60  fof(f394,plain,(
% 0.22/0.60    spl4_31 | spl4_1 | ~spl4_22),
% 0.22/0.60    inference(avatar_split_clause,[],[f389,f288,f55,f363])).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    spl4_1 <=> sK0 = sK3),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.60  fof(f288,plain,(
% 0.22/0.60    spl4_22 <=> r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.60  fof(f389,plain,(
% 0.22/0.60    sK1 = sK3 | (spl4_1 | ~spl4_22)),
% 0.22/0.60    inference(subsumption_resolution,[],[f385,f57])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    sK0 != sK3 | spl4_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f55])).
% 0.22/0.60  fof(f385,plain,(
% 0.22/0.60    sK0 = sK3 | sK1 = sK3 | ~spl4_22),
% 0.22/0.60    inference(resolution,[],[f290,f30])).
% 0.22/0.60  fof(f290,plain,(
% 0.22/0.60    r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1)) | ~spl4_22),
% 0.22/0.60    inference(avatar_component_clause,[],[f288])).
% 0.22/0.60  fof(f361,plain,(
% 0.22/0.60    spl4_30 | ~spl4_5 | ~spl4_26),
% 0.22/0.60    inference(avatar_split_clause,[],[f354,f333,f82,f358])).
% 0.22/0.60  fof(f333,plain,(
% 0.22/0.60    spl4_26 <=> sK1 = sK2),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.60  fof(f354,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK3) | (~spl4_5 | ~spl4_26)),
% 0.22/0.60    inference(backward_demodulation,[],[f84,f335])).
% 0.22/0.60  fof(f335,plain,(
% 0.22/0.60    sK1 = sK2 | ~spl4_26),
% 0.22/0.60    inference(avatar_component_clause,[],[f333])).
% 0.22/0.60  fof(f84,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl4_5),
% 0.22/0.60    inference(avatar_component_clause,[],[f82])).
% 0.22/0.60  fof(f336,plain,(
% 0.22/0.60    spl4_26 | spl4_2 | ~spl4_21),
% 0.22/0.60    inference(avatar_split_clause,[],[f331,f283,f60,f333])).
% 0.22/0.60  fof(f283,plain,(
% 0.22/0.60    spl4_21 <=> r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.60  fof(f331,plain,(
% 0.22/0.60    sK1 = sK2 | (spl4_2 | ~spl4_21)),
% 0.22/0.60    inference(subsumption_resolution,[],[f328,f62])).
% 0.22/0.60  fof(f328,plain,(
% 0.22/0.60    sK0 = sK2 | sK1 = sK2 | ~spl4_21),
% 0.22/0.60    inference(resolution,[],[f285,f30])).
% 0.22/0.60  fof(f285,plain,(
% 0.22/0.60    r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | ~spl4_21),
% 0.22/0.60    inference(avatar_component_clause,[],[f283])).
% 0.22/0.60  fof(f323,plain,(
% 0.22/0.60    spl4_22 | ~spl4_5),
% 0.22/0.60    inference(avatar_split_clause,[],[f317,f82,f288])).
% 0.22/0.60  fof(f317,plain,(
% 0.22/0.60    r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1)) | ~spl4_5),
% 0.22/0.60    inference(superposition,[],[f49,f84])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.22/0.60    inference(equality_resolution,[],[f34])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f23])).
% 0.22/0.60  % (3895)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  fof(f322,plain,(
% 0.22/0.60    spl4_21 | ~spl4_5),
% 0.22/0.60    inference(avatar_split_clause,[],[f316,f82,f283])).
% 0.22/0.60  fof(f316,plain,(
% 0.22/0.60    r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | ~spl4_5),
% 0.22/0.60    inference(superposition,[],[f44,f84])).
% 0.22/0.60  fof(f252,plain,(
% 0.22/0.60    spl4_17 | spl4_17 | ~spl4_14),
% 0.22/0.60    inference(avatar_split_clause,[],[f248,f143,f250,f250])).
% 0.22/0.60  fof(f143,plain,(
% 0.22/0.60    spl4_14 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.60  fof(f248,plain,(
% 0.22/0.60    ( ! [X0,X1] : (sK0 = X0 | sK0 = X1) ) | ~spl4_14),
% 0.22/0.60    inference(subsumption_resolution,[],[f243,f70])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.60    inference(trivial_inequality_removal,[],[f69])).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.60    inference(superposition,[],[f38,f43])).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.60    inference(nnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.60  fof(f243,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK0 = X0 | sK0 = X1) ) | ~spl4_14),
% 0.22/0.60    inference(superposition,[],[f30,f145])).
% 0.22/0.60  fof(f145,plain,(
% 0.22/0.60    k1_xboole_0 = k1_tarski(sK0) | ~spl4_14),
% 0.22/0.60    inference(avatar_component_clause,[],[f143])).
% 0.22/0.60  fof(f241,plain,(
% 0.22/0.60    spl4_1 | ~spl4_8),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f229])).
% 0.22/0.60  fof(f229,plain,(
% 0.22/0.60    $false | (spl4_1 | ~spl4_8)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f57,f106,f36])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != k1_tarski(X0) | X0 = X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (X0 = X1 | k2_tarski(X1,X2) != k1_tarski(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f11])).
% 0.22/0.60  fof(f11,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 0.22/0.60  fof(f106,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK3) | ~spl4_8),
% 0.22/0.60    inference(avatar_component_clause,[],[f104])).
% 0.22/0.60  fof(f204,plain,(
% 0.22/0.60    spl4_2 | ~spl4_7),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.60  fof(f193,plain,(
% 0.22/0.60    $false | (spl4_2 | ~spl4_7)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f62,f102,f36])).
% 0.22/0.60  fof(f102,plain,(
% 0.22/0.60    k2_tarski(sK0,sK1) = k1_tarski(sK2) | ~spl4_7),
% 0.22/0.60    inference(avatar_component_clause,[],[f100])).
% 0.22/0.60  fof(f165,plain,(
% 0.22/0.60    spl4_14 | ~spl4_6),
% 0.22/0.60    inference(avatar_split_clause,[],[f164,f96,f143])).
% 0.22/0.60  fof(f164,plain,(
% 0.22/0.60    k1_xboole_0 = k1_tarski(sK0) | ~spl4_6),
% 0.22/0.60    inference(subsumption_resolution,[],[f159,f70])).
% 0.22/0.60  fof(f159,plain,(
% 0.22/0.60    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0) | ~spl4_6),
% 0.22/0.60    inference(superposition,[],[f75,f98])).
% 0.22/0.60  fof(f98,plain,(
% 0.22/0.60    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl4_6),
% 0.22/0.60    inference(avatar_component_clause,[],[f96])).
% 0.22/0.60  fof(f75,plain,(
% 0.22/0.60    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X2,X3),k1_tarski(X2)) | k1_tarski(X2) = k2_tarski(X2,X3)) )),
% 0.22/0.60    inference(resolution,[],[f42,f44])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.60    inference(flattening,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.60    inference(nnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.60  fof(f68,plain,(
% 0.22/0.60    spl4_3),
% 0.22/0.60    inference(avatar_split_clause,[],[f27,f65])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.60    inference(cnf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f20])).
% 0.22/0.60  % (3908)Refutation not found, incomplete strategy% (3908)------------------------------
% 0.22/0.60  % (3908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (3895)Refutation not found, incomplete strategy% (3895)------------------------------
% 0.22/0.61  % (3895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (3895)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (3895)Memory used [KB]: 1663
% 0.22/0.61  % (3895)Time elapsed: 0.131 s
% 0.22/0.61  % (3895)------------------------------
% 0.22/0.61  % (3895)------------------------------
% 0.22/0.61  % (3923)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.61  % (3910)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.61  % (3906)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.61  % (3919)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.61  % (3908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (3910)Refutation not found, incomplete strategy% (3910)------------------------------
% 0.22/0.61  % (3910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (3910)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (3910)Memory used [KB]: 10618
% 0.22/0.61  % (3910)Time elapsed: 0.182 s
% 0.22/0.61  % (3910)------------------------------
% 0.22/0.61  % (3910)------------------------------
% 0.22/0.61  % (3908)Memory used [KB]: 1918
% 0.22/0.61  % (3908)Time elapsed: 0.165 s
% 0.22/0.61  % (3908)------------------------------
% 0.22/0.61  % (3908)------------------------------
% 0.22/0.61  % (3921)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.61  % (3906)Refutation not found, incomplete strategy% (3906)------------------------------
% 0.22/0.61  % (3906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (3906)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (3906)Memory used [KB]: 10618
% 0.22/0.61  % (3906)Time elapsed: 0.181 s
% 0.22/0.61  % (3906)------------------------------
% 0.22/0.61  % (3906)------------------------------
% 0.22/0.61  fof(f20,plain,(
% 0.22/0.61    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.22/0.61    introduced(choice_axiom,[])).
% 0.22/0.61  fof(f15,plain,(
% 0.22/0.61    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.61    inference(ennf_transformation,[],[f14])).
% 0.22/0.61  fof(f14,negated_conjecture,(
% 0.22/0.61    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.61    inference(negated_conjecture,[],[f13])).
% 0.22/0.61  fof(f13,conjecture,(
% 0.22/0.61    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.22/0.61  fof(f63,plain,(
% 0.22/0.61    ~spl4_2),
% 0.22/0.61    inference(avatar_split_clause,[],[f28,f60])).
% 0.22/0.61  fof(f28,plain,(
% 0.22/0.61    sK0 != sK2),
% 0.22/0.61    inference(cnf_transformation,[],[f21])).
% 0.22/0.61  fof(f58,plain,(
% 0.22/0.61    ~spl4_1),
% 0.22/0.61    inference(avatar_split_clause,[],[f29,f55])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    sK0 != sK3),
% 0.22/0.61    inference(cnf_transformation,[],[f21])).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (3915)------------------------------
% 0.22/0.61  % (3915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (3915)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (3915)Memory used [KB]: 6524
% 0.22/0.61  % (3915)Time elapsed: 0.171 s
% 0.22/0.61  % (3915)------------------------------
% 0.22/0.61  % (3915)------------------------------
% 1.73/0.61  % (3904)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.73/0.61  % (3893)Success in time 0.242 s
%------------------------------------------------------------------------------
